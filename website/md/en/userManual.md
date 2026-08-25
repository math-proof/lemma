# User Manual — Lean 4 Formal Theorem Library

## Online usage

### Theorem search

The Lean 4 visualization site is served by `index.php` at the repository root (typical local URLs: [http://localhost:8080/lean/index.php](http://localhost:8080/lean/index.php) or [http://localhost/lean/index.php](http://localhost/lean/index.php), depending on your PHP document root and port). With no query parameters, the library summary is shown; use the search box (top right) or a GET URL to search.

**Basic search** matches module names in the database (substring match; at most `limit` hits, default 100). Examples:

- [../../../index.php?q=Icc&limit=100](../../../index.php?q=Icc&limit=100) — modules whose name contains `Icc`
- [../../../index.php?q=kv_cache&limit=50](../../../index.php?q=kv_cache&limit=50) — modules whose name contains `kv_cache`
- [../../../index.php?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T](../../../index.php?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T) — open the main KV-cache lemma directly

The search placeholder reads `input a hint in search of a formula/theorem/axiom`. Optional flags (checkboxes or URL parameters):

- `limit` — maximum number of results (default 100)
- `caseSensitive=on` — case-sensitive match
- `wholeWord=on` — whole-word match
- `regularExpression=on` — regular expression (e.g. `q=Tensor\..*BandPart&regularExpression=on`)
- `fullText=on` — grep in `Lemma/**/*.lean` sources (e.g. `q=band_part&fullText=on`)
- `latex=on` — LaTeX formula similarity search (requires the LaTeX backend service)

Shortcuts (with focus in the search box): Alt+C / W / R / L / U toggle Case / WholeWord / Regex / LaTeX / FullText; Ctrl+F focuses the search box.

![search box](png/search/panel.png)

Enter a keyword (e.g. module fragment `Icc`, `DotSoftmax`, `kv_cache`) and submit to list matching modules; click a result to open that lemma page.

![search keyword](png/search/keyword.png)

The results page title is `search results` with a hit count. Click a module name to open its given / imply / proof view.

![search results](png/search/results.png)

### Lemma dependencies (callee / caller)

Each lemma page has three blocks: **-- given**, **-- imply**, and **-- proof**. Dependencies come from the `imports` field in the database: if lemma A’s `imports` contains `Lemma.B`, then A uses B in its proof.

Terminology (English labels and URL parameters on the site):

- **callee hierarchy** (link on the `-- imply` heading, `?callee=module`): lemmas that *import this module* — other results whose `imports` list includes the current module (who depends on this result).
- **caller hierarchy** (link on the `-- proof` heading, `?caller=module`): lemmas *imported by this module* — entries in this module’s `imports` list (what this proof calls).

On the hierarchy page you can switch between callee and caller views; append `#deep` or use the deep link to expand the full tree; use `>>>>` / `<<<<` beside nodes to expand or collapse one level.

#### Callee hierarchy (who uses this lemma)

Example: the [main KV-cache lemma](../../../index.php?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T).

On the lemma page, hover the link left of **-- imply**; the tooltip is `callee hierarchy`:

![callee link](png/hierarchy/hyperlink.png)

Click it to open the callee graph, e.g. [`?callee=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T`](../../../index.php?callee=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T):

![callee hierarchy](png/hierarchy/callee.png)

The graph lists other lemmas whose `imports` reference this module (if any).

- Click `>>>>` to expand further dependents; `<<<<` to collapse.
- Open [`?callee=…#deep`](../../../index.php?callee=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T#deep) to expand the full callee tree at once.

#### Caller hierarchy (what this lemma uses)

On the lemma page, click the link left of **-- proof** titled `caller hierarchy`, e.g. [`?caller=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T`](../../../index.php?caller=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T):

![caller hierarchy](png/hierarchy/caller.png)

The graph lists lemmas imported in this proof (e.g. `Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T` (lemma `gpt`), `Tensor.Stack.eq.AppendStackS`, etc.).

- Open [`?caller=…#deep`](../../../index.php?caller=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T#deep) to expand the full caller tree.

![deep caller hierarchy](png/hierarchy/deep/caller.png)

## Local deployment

You need a PHP web server, MySQL (theorem index), the Lean 4 toolchain, and this repository [math-proof/lemma](https://github.com/math-proof/lemma). Point PHP `DocumentRoot` at the cloned repo root (containing `index.php` and `Lemma/`).

Linux example (see [php installation.docx](../php%20installation.docx) for PHP setup):

```bash
cd /usr/local
git clone https://github.com/cosmosZhou/shell.git
cd shell/php
make
sh start.sh port=80 DocumentRoot=/home/github/lean
```

Windows example:

1. Set the web root, e.g. `E:\github\lean`, and configure `DOCUMENT_ROOT` per php installation.docx.
2. Clone the project: `git clone --depth=1 https://github.com/math-proof/lemma.git`
3. Install Lean 4 (see `lean-toolchain`), run `lake build`, and refresh the MySQL index (e.g. `ps1/update.ps1`).
4. In the browser (adjust port as configured):
   - [http://localhost/lean/index.php](http://localhost/lean/index.php)
   - or [http://localhost:8080/lean/index.php?q=Icc&limit=100](http://localhost:8080/lean/index.php?q=Icc&limit=100)
