# AGENTS

## Screenslaver

A Screenslaver daemon runs at `http://localhost:3000` for browser automation and screenshots.

Use it for any local app port by substituting the target URL, for example `http://localhost:5176/`.

### Create a session

```bash
curl -s -X POST http://localhost:3000/sessions \
  -H 'Content-Type: application/json' \
  -d '{"name":"local-app","url":"http://localhost:5176/","viewport":{"width":1440,"height":900}}'
```

### Run actions

```bash
curl -s -X POST http://localhost:3000/sessions/local-app/actions \
  -H 'Content-Type: application/json' \
  -d '{"actions":[{"action":"html"},{"action":"console"},{"action":"screenshot"}]}'
```

### Navigate and interact

Use a heredoc when values contain special characters.

```bash
curl -s -X POST http://localhost:3000/sessions/local-app/actions \
  -H 'Content-Type: application/json' \
  -d @- <<'EOF'
{"actions":[
  {"action":"goto","url":"http://localhost:5176/"},
  {"action":"wait","ms":1000},
  {"action":"click","selector":"text=Some text"},
  {"action":"fill","selector":"input","value":"example"},
  {"action":"waitFor","selector":".some-selector"},
  {"action":"screenshot"}
]}
EOF
```

### Available actions

`goto`, `click`, `fill`, `scroll`, `wait`, `waitFor`, `screenshot`, `html`, `console`

### Screenshots

Screenshot responses include a `"path"` field with an absolute path to the saved image. Use the image viewer tool on that path to inspect it.

### Teardown

```bash
curl -s -X DELETE http://localhost:3000/sessions/local-app
```
