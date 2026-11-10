"""Rebuild checked-in VMTs; original inventory and source bytes stay untouched."""

import argparse
from collections import Counter
import json
from pathlib import Path
import sys

from . import cubicle, ivy, ivy_vmt, mcmt, mypyvy
from .core import Unsupported, sha256


ROOT = Path(__file__).resolve().parents[2] / 'examples' / 'quantified-transition-systems'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--check', action='store_true', help='verify regeneration without writing')
    parser.add_argument('--only', help='source path substring for a partial local conversion (no manifest update)')
    args = parser.parse_args()
    root = args.root
    inventory = json.loads((root / 'manifest.json').read_text())
    target = root / 'generated-vmt'
    manifest = {'schema_version': 1, 'generator': 'tools.benchmark_translation',
                'validation': 'SMT-LIB syntax and type checking, not a general equivalence proof',
                'entries': []}
    package = Path(__file__).parent
    generator_files = sorted([*package.glob('*.py'), package / 'requirements.txt',
                              *[p for p in (package / 'vendor').rglob('*')
                                if p.is_file() and '__pycache__' not in p.parts]])
    manifest['generator_sha256'] = {p.relative_to(package).as_posix(): sha256(p.read_bytes())
                                    for p in generator_files}
    mismatch = []
    generated = set()

    def save(relative, data):
        path = target / relative
        if args.check:
            if not path.exists() or path.read_bytes() != data:
                mismatch.append(relative)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)

    models = inventory['benchmarks']
    by_path = {r['path']: r for r in models}
    for row in models:
        path = row['path']
        if args.only and args.only not in path:
            continue
        ext = Path(path).suffix
        kind, converter = None, None
        if path.startswith('mypyvy/') and ext == '.pyv':
            kind, converter = 'mypyvy', mypyvy.convert
        elif ext == '.cub':
            kind, converter = 'cubicle', cubicle.convert
        elif ext in ('.in', '.mcmt'):
            kind, converter = 'mcmt-lambda-profile', mcmt.convert
        elif path.startswith('ivybench/') and ext == '.vmt':
            kind, converter = 'ivy-action-vmt', ivy_vmt.convert
        elif path.startswith('ivybench/multisig/') and ext == '.ivy':
            kind, converter = 'ivy-multisig', ivy.convert
        elif path.startswith('ivybench/') and ext in ('.ivy', '.pyv'):
            # The upstream compiler's checked-in companion is the canonical
            # translation input. Do not pretend we recompiled general Ivy.
            companion = str(Path(path).parent.parent / 'vmt' / (Path(path).stem + '.vmt'))
            if companion not in by_path:
                raise RuntimeError(f'missing companion for {path}')
            original = (root / path).read_bytes()
            if sha256(original) != row['sha256']:
                raise RuntimeError(f'source hash mismatch: {path}')
            manifest['entries'].append({'source':path, 'source_sha256':row['sha256'],
                                        'status':'upstream-companion', 'translation_input':companion,
                                        'output':companion + '.vmt'})
            continue
        else:
            continue
        original = (root / path).read_bytes()
        if sha256(original) != row['sha256']:
            raise RuntimeError(f'source hash mismatch: {path}')
        entry = {'source':path, 'source_sha256':row['sha256'], 'frontend':kind}
        try:
            model = converter(original.decode('utf-8'))
            if path == 'cubicle/examples/distrib_channels.cub':
                model.notes.append('Known source issue: init requires Channel_v[z,z1] = 1.0 AND = 0.0; initial state is empty. Preserved for audit, not a meaningful safety success.')
            model.validate()
            data = model.render(path, row['sha256']).encode()
        except Unsupported as error:
            entry.update(status='unsupported', reason=str(error))
        else:
            output = path + '.vmt'
            save(output, data)
            generated.add(output)
            entry.update(status='generated', output=output, output_sha256=sha256(data),
                         actions=len(model.actions), properties=len(model.properties), notes=model.notes)
        manifest['entries'].append(entry)
    if not args.only:
        # Stale output is never silently retained as a current successful import.
        for path in target.rglob('*.vmt'):
            relative = path.relative_to(target).as_posix()
            if relative not in generated:
                raise RuntimeError(f'stale generated output; review/remove explicitly: {path}')
        manifest['summary'] = dict(sorted(Counter(e['status'] for e in manifest['entries']).items()))
        save('manifest.json', (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode())
        save('vmt-inputs.txt', ('\n'.join(sorted(generated)) + '\n').encode())
        print(json.dumps(manifest['summary'], sort_keys=True))
    if mismatch:
        print('Regeneration differs: ' + ', '.join(mismatch), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
