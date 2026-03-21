# Node server (`server/app.mjs`)

## Run (no PHP / Apache)

```bash
npm install
npm start
```

Open:

`http://127.0.0.1:3000/lean/?module=Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax`

Static assets: `/lean/static/...` (served from `./static`).

### What runs in Node

- Resolves `module` → `Lemma/<path>.lean`.
- Builds the `render` Vue payload via **`server/lean/compiler/index.mjs`**:
  - **`LEAN_COMPILER=auto`** (default): if `php` is on `PATH`, runs **`server/lean/php-bridge/render2vue.php`** (real PHP **`compile` → `render2vue(false)`**, same as `php/lemma.php`); otherwise uses **`parseLeanStub.mjs`**.
  - **`LEAN_COMPILER=stub`**: always the regex stub.
  - **`LEAN_COMPILER=php`**: always PHP (errors if PHP missing).
- Renders **`views/lemma.ejs`** (same script/CSS idea as `php/lemma.php`).

See **`server/lean/compiler/README.md`** for **`echo2vueFromModule`** (PHP bridge) vs a full JS port of `lean.php` (incremental).

---

## Environment

| Variable | Default | Meaning        |
|----------|---------|----------------|
| `PORT`   | `3000`  | Listen port    |
