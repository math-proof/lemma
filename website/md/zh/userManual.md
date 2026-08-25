# Lean 4 形式化定理库操作手册

## 线上操作

### 定理检索

Lean 4 可视化定理库由仓库根目录的 `index.php` 提供（本地常见地址：[http://localhost:8080/lean/index.php](http://localhost:8080/lean/index.php) 或 [http://localhost/lean/index.php](http://localhost/lean/index.php)，视 PHP 站点根目录与端口而定）。打开后若无查询参数，显示定理库摘要；在页面右上角的搜索框输入关键词并提交，或直接使用 GET 链接检索。

**基本检索**：在模块名数据库中做子串匹配（默认最多返回 `limit` 条，缺省为 100）。示例：

- [../../../index.php?q=Icc&limit=100](../../../index.php?q=Icc&limit=100) — 模块名含 `Icc` 的引理
- [../../../index.php?q=kv_cache&limit=50](../../../index.php?q=kv_cache&limit=50) — 模块名含 `kv_cache`
- [../../../index.php?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T](../../../index.php?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T) — 直接打开 KV-cache 主引理页

搜索框占位符为 `input a hint in search of a formula/theorem/axiom`。可选参数（勾选或写入 URL）：

- `limit` — 结果条数上限（默认 100）
- `caseSensitive=on` — 区分大小写
- `wholeWord=on` — 全词匹配
- `regularExpression=on` — 正则表达式（例：`q=Tensor\..*BandPart&regularExpression=on`）
- `fullText=on` — 在 `Lemma/**/*.lean` 源文件中全文检索（例：`q=band_part&fullText=on`）
- `latex=on` — 按 LaTeX 公式相似度检索（需后端 LaTeX 服务）

快捷键（搜索框聚焦时）：Alt+C / W / R / L / U 分别切换 Case / WholeWord / Regex / LaTeX / FullText；Ctrl+F 聚焦搜索框。

![搜索框](png/search/panel.png)

在搜索框输入关键词（如模块名片段 `Icc`、`DotSoftmax`、`kv_cache`），提交后即可列出匹配的模块名；单击结果中的链接进入对应引理页。

![搜索关键词](png/search/keyword.png)

结果页标题为 `search results`，并显示命中条数。单击某一模块名打开该定理的 given / imply / proof 页面。

![搜索结果](png/search/results.png)

### 引理依存关系（callee / caller）

每条引理页分为 **-- given**、**-- imply**、**-- proof** 三块。依存关系由数据库中的 `imports` 字段维护：若引理 A 的 `imports` 含 `Lemma.B`，则 A 在证明中使用了 B。

术语与链接（页面上的英文标题与 URL 参数一致）：

- **callee hierarchy**（`-- imply` 标题上的链接，`?callee=模块名`）：*引用本定理的引理* — 即 `imports` 中包含本模块的其他引理（谁依赖本结果）。
- **caller hierarchy**（`-- proof` 标题上的链接，`?caller=模块名`）：*本定理所引用的引理* — 即本模块 `imports` 列表中的引理（本证明调用了谁）。

可在层级页顶部在 callee 与 caller 视图之间切换；链接 `#deep` 或页面上的 deep 选项可展开完整多层依存树；子节点旁的 `>>>>` / `<<<<` 可逐层展开或折叠。

#### callee 层级（谁使用了本定理）

以下以 [KV-cache 主引理](../../../index.php?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T) 为例。

在引理页将鼠标悬停于 **-- imply** 左侧链接，提示为 `callee hierarchy`：

![callee 链接](png/hierarchy/hyperlink.png)

单击该链接进入 callee 层级图，例如 [`?callee=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T`](../../../index.php?callee=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T)：

![callee 层级图](png/hierarchy/callee.png)

图中列出在 `imports` 中引用该模块的其他引理（若有）。

- 单击 `>>>>` 展开更上层引用；`<<<<` 折叠。
- 访问 [`?callee=…#deep`](../../../index.php?callee=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T#deep) 可一次展开全部 callee 层级。

#### caller 层级（本定理使用了谁）

在引理页单击 **-- proof** 左侧、标题为 `caller hierarchy` 的链接，例如 [`?caller=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T`](../../../index.php?caller=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T)：

![caller 层级图](png/hierarchy/caller.png)

图中列出该引理证明所 import 的子引理（如 `Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T`（lemma `gpt`）、`Tensor.Stack.eq.AppendStackS` 等）。

- 访问 [`?caller=…#deep`](../../../index.php?caller=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T#deep) 可展开完整 caller 层级。

![caller 深层展开](png/hierarchy/deep/caller.png)

## 线下部署与使用

本地运行需：PHP Web 服务器、MySQL（定理索引库）、Lean 4 工具链，以及本仓库 [math-proof/lemma](https://github.com/math-proof/lemma)。将 PHP 的文档根目录（`DocumentRoot`）指向克隆下来的仓库根目录（内含 `index.php` 与 `Lemma/`）。

Linux 示例（PHP 安装细节见 [php installation.docx](../php%20installation.docx)）：

```bash
cd /usr/local
git clone https://github.com/cosmosZhou/shell.git
cd shell/php
make
sh start.sh port=80 DocumentRoot=/home/github/lean
```

Windows 示例：

1. 指定网页根目录，例如 `E:\github\lean`，按 php installation.docx 配置 `DOCUMENT_ROOT`。
2. 克隆工程：`git clone --depth=1 https://github.com/math-proof/lemma.git`
3. 安装 Lean 4（见仓库 `lean-toolchain`），执行 `lake build`，并按项目脚本更新 MySQL 定理索引（如 `ps1/update.ps1`）。
4. 浏览器访问（端口按本地配置调整）：
   - [http://localhost/lean/index.php](http://localhost/lean/index.php)
   - 或 [http://localhost:8080/lean/index.php?q=Icc&limit=100](http://localhost:8080/lean/index.php?q=Icc&limit=100)
