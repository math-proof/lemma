# Node server (`server/app.mjs`)

## Run (no PHP / Apache)

```bash
npm install
npm start
```

Open:

`http://127.0.0.1/lean/?module=Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax`

Static assets: `/lean/static/...` (served from `./static`).

### What runs in Node

- Resolves `module` → `Lemma/<path>.lean`.
- Builds the `render` Vue payload via **`server/lean/compiler/index.mjs`** (JS `compile()` + `render2vue.mjs`; falls back to regex stub when parse fails).
- Renders **`views/lemma.ejs`** (same script/CSS idea as `php/lemma.php`).

See **`server/lean/compiler/README.md`** for details.

---

## Environment

| Variable | Default | Meaning        |
|----------|---------|----------------|
| `PORT`   | `80`    | Listen port    |
