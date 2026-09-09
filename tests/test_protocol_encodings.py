"""Soundness-sensitive substitution and outcome-accounting regressions."""

import unittest
from pathlib import Path

from scripts.compare_protocol_encodings import classify
from scripts.encode_distributed_protocols import Encoder, contains_lambda, dump, encode, free_vars, parse_spans


def parse(text):
    return parse_spans(text)[0][0]


class ProtocolEncodingTests(unittest.TestCase):
    def encoder(self):
        return Encoder([parse("(declare-sort S 0)"),
                        parse("(declare-fun A () (Array S Bool))"),
                        parse("(declare-fun v () S)")])

    def test_let_expansion_does_not_capture_a_free_variable(self):
        encoded = self.encoder().expand(parse("(let ((x y)) (forall ((y S)) (= x y)))"))
        binder = encoded[1][0][0]
        self.assertNotEqual(binder, "y")
        self.assertEqual(encoded[2], ["=", "y", binder])
        self.assertIn("y", free_vars(encoded))

    def test_let_bindings_are_simultaneous_and_nested_shadowing_is_preserved(self):
        term = parse("(let ((x a)) (let ((x b) (y x)) (= x y)))")
        self.assertEqual(self.encoder().expand(term), ["=", "b", "a"])

    def test_quoted_and_unquoted_variable_aliases_do_not_break_capture_avoidance(self):
        term = parse("(let ((|x| y)) (forall ((|y| S)) (= x |y|)))")
        result = self.encoder().expand(term)
        binder = result[1][0][0]
        self.assertNotEqual(binder, "|y|")
        self.assertEqual(result[2], ["=", "y", binder])

    def test_beta_reduction_renames_a_conflicting_inner_binder(self):
        term = parse("(lambda ((x S)) (lambda ((y S)) (= x y)))")
        result = self.encoder().read(term, "y")
        binder = result[1][0][0]
        self.assertNotEqual(binder, "y")
        self.assertEqual(result[2], ["=", "y", binder])

    def test_array_disequality_keeps_negation_outside_the_universal(self):
        result = self.encoder().rewrite(parse("(not (= A (lambda ((x S)) (= x v))))"))
        self.assertEqual(result[0], "not")
        self.assertEqual(result[1][0], "forall")
        self.assertFalse(contains_lambda(result))
        self.assertFalse(any(s.startswith("encoding.index.") for s in free_vars(result)))

    def test_selecting_a_lambda_uses_the_selected_index(self):
        result = self.encoder().rewrite(parse("(select (lambda ((x S)) (= x v)) v)"))
        self.assertEqual(result, ["=", "v", "v"])

    def test_generated_indices_cannot_shadow_original_symbols(self):
        for symbol in ("|encoding.index.0|", "encoding.index.0"):
            encoder = Encoder([parse(f"(declare-fun {symbol} () S)")])
            self.assertNotEqual(encoder.fresh(), "|encoding.index.0|")

    def test_unaffected_commands_remain_byte_identical(self):
        source = "; comment\n(declare-fun A () (Array S Bool))\n(assert   true)\n"
        result, _, changed = encode(source)
        self.assertEqual(result, source)
        self.assertEqual(changed, 0)

    def test_all_companions_are_lambda_free_and_introduce_no_free_symbols(self):
        paths = sorted(Path("examples/distributed_protocols").glob("*/*.encoding.vmt"))
        originals = [p for p in Path("examples/distributed_protocols").glob("*/*.vmt")
                     if not p.name.endswith(".encoding.vmt")]
        self.assertEqual({p.with_suffix(".encoding.vmt") for p in originals}, set(paths))
        for path in paths:
            with self.subTest(path=path):
                original = path.with_name(path.name.replace(".encoding.vmt", ".vmt"))
                source_commands = [n for n, _, _ in parse_spans(original.read_text())]
                encoded_commands = [n for n, _, _ in parse_spans(path.read_text())]
                self.assertFalse(contains_lambda(encoded_commands))
                self.assertEqual(len(source_commands), len(encoded_commands))
                for before, after in zip(source_commands, encoded_commands):
                    self.assertEqual(before[:1], after[:1])
                    if before[0].startswith("declare"):
                        self.assertEqual(before, after)
                    self.assertFalse(any(s.startswith("encoding.index.")
                                         for s in free_vars(after)), dump(after))


if __name__ == "__main__":
    unittest.main()
