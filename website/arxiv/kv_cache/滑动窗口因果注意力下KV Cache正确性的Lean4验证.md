项目工件：<https://github.com/math-proof/lemma>

# 摘要

生产级 GPT 式解码器依赖 key–value（KV）cache，以避免在每一步自回归解码中重复计算过去的 key 与 value。Hugging Face Transformers、vLLM 及相关系统将 cache 张量与新 token 拼接，并在滑动因果窗口上计算注意力，但这一增量更新靠测试验证，而非证明为张量恒等式。

我们在 `lemma` 库中陈述并机器检验如下恒等式：若每个前缀输出 \(Z(n)\) 等于滑动窗口 masked scaled dot-product attention，则 \(Z(n+1)\) 等于 \(Z(n)\) 再拼接一行——该行由 cache 窗口与新 key/value 算出的 attention 行。证明于 **2026-08-19** 在 Lean 4 中检验完成；**2024-02-28** 起已有 SymPy 交互表述。

掩码通过 `band_part` 在超实数上使用 \(-\infty\)（由 `tril` / `triu` / `masked_fill` 定义，遵循 TensorFlow 的 [`tf.linalg.band_part`](https://tensorflow.google.cn/api_docs/python/tf/linalg/band_part)）；相等性为本库在 \(\mathbb{R}^*\) 上全定义的 closeness 关系 \(\approx\)，设计上 mimic [`torch.isclose`](https://docs.pytorch.org/docs/stable/generated/torch.isclose.html)。

下文给出形式陈述、证明思路、引理依赖结构，以及主张与不主张的边界。交互式可视化与源码公开于 [lemma.cn](http://www.lemma.cn/) 与 [GitHub](https://github.com/math-proof/lemma)。

# 1 引言

GPT-2、GPT-3、GPT-4 以及 Hugging Face 的每个 `AutoModelForCausalLM` 均逐 token 解码。每一步，自注意力层将隐状态映射为 query、key、value（\(Q,K,V\)）。对位置 \(n\) 的新 token，因果注意力为

\[
\operatorname{softmax}\!\left(\frac{q_n K_{:n+1}^{\top}}{\sqrt{d_z}}+M\right)V_{:n+1},
\]

其中 \(K_{:n+1}\)、\(V_{:n+1}\) 收集迄今全部 token 的 key 与 value，\(M\) 屏蔽未来位置。产生 \(K,V\) 的线性映射不依赖后续 token，故前 \(n\) 行 key/value 永不改变；每步 generate 对前缀重算的成本随前缀长度平方增长，纯属浪费。

*KV cache* 缓存过去的 key 与 value，下一步仅拼接新一对：

\[
K_{:n+1}=K_{:n}\mathbin{+\mkern-4mu+}[k_n],\qquad V_{:n+1}=V_{:n}\mathbin{+\mkern-4mu+}[v_n].
\]

Hugging Face Transformers 以 `use_cache=True` 实现（[`generate`](https://huggingface.co/docs/transformers/en/main_classes/text_generation) 的默认值）。张量以 `past_key_values` 传递；默认容器为 [`DynamicCache`](https://huggingface.co/docs/transformers/en/kv_cache)，每层一对 \((K,V)\)，形状 `[batch, heads, seq_len, head_dim]`。注意力模块内部将当前 \(k,v\) 与 cache 拼接，在长度为 `past_kv_length + 1` 的 mask 上计算（[cache 说明](https://huggingface.co/docs/transformers/en/cache_explanation)）。Prefill 对整段 prompt 运行一次；decode 则每步输入一个新 `input_id` 与 cache。滑动窗口模型只保留最近 \(\ell\) 对，与本文 Lean 陈述一致；经典 GPT 保留全前缀，与 SymPy 特例一致。

这是实现。本文贡献是缺失的代数恒等式：若 \(Z(n)\) 已是前缀的 masked attention，则「将 cache 与新 \(k,v\) 拼接并取最后一行」恰为 \(Z(n+1)\)，而非另一算法。我们在语义等价于 `torch.Tensor` 的 `Tensor` 类型中，将其证明为机器检验引理；因果 mask 为超实数 \(\mathbb{R}^*\) 上的 \((\operatorname{band\_part}-1)\cdot\infty\)，使被 mask 位置在 \(\exp\) 后为 0，而非浮点替身 \(-10^9\)。

公开交互陈述见 lemma.cn 的 [SymPy](http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache) 与 [Lean 4](http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T)；源码文件为 `All_Eq_DotSoftmaxAdd_DivDot_T.lean` 与 `kv_cache.py`（[GitHub](https://github.com/math-proof/lemma)）。

# 2 相关工作

**运行时系统。** PyTorch、Hugging Face Transformers（[cache 说明](https://huggingface.co/docs/transformers/en/cache_explanation)）、[vLLM](https://github.com/vllm-project/vllm) 与 [SGLang](https://arxiv.org/abs/2312.07104) 将 KV cache 与滑动窗口实现为生产系统。正确性靠测试，而非证明为张量方程。

**形式化库。** [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) 有超实数分析，但无 `torch.Tensor` 演算、无 `band_part`、无与 PyTorch 语义一致的 softmax-attention 引理。OrthoCache 机器检验 Walsh–Hadamard 变换的 Parseval 与谱 eviction 的全变差界；**未**证明增量 cache 一行等于全 masked attention。TorchLean / BatchInvariantInference 指定 schedule 显式的 CUDA attention 与 batch 不变性——属于 kernel 对指称的 refinement，而非本库带 `band_part` 与超实数 \(\infty\) 的 `Tensor` 恒等式。`fak` 项目在 Go 中报告 bit 一致的 cache 测试（\(\max|\Delta|=0\)）；属经验见证，非 Lean/SymPy 定理。

**超实数 closeness。** 经典非标准分析（Keisler）与 Mathlib 以 \(a-b\) 无穷小定义「无穷接近」，等价于两者有限时 \(\operatorname{st}(a)=\operatorname{st}(b)\)。无穷超实数无 standard part，该关系在 \(\mathbb{R}^*\) 上不全。[`torch.isclose`](https://docs.pytorch.org/docs/stable/generated/torch.isclose.html) 是 IEEE 浮点代码：\(|x-y|\le \mathrm{rtol}\cdot|y|+\mathrm{atol}\)；非有限值 close 当且仅当相等。它既非定理，也非超实数语义。

本库的 \(\approx\) 关系（[`Hyperreal.XEq.is.InfinitesimalDivAbsSub`](http://www.lemma.cn/lean/?module=Hyperreal.XEq.is.InfinitesimalDivAbsSub)）填补这一空白：在 \(\mathbb{R}^*\) 上全定义、可机器检验，以无穷小相对容差 mimic `torch.isclose`。KV cache 引理是首批大规模使用该关系的张量恒等式之一：\(\exp(-\infty)\approx 0\)，masked softmax 与窗口堆叠在 \(\mathbb{R}\) 中不等义相等，但在 \(\approx\) 下成立。

# 3 预备知识

## 3.1 张量与记号

`Tensor ℝ s` 为本库对形状 `s` 的实张量形式化，运算与 `torch.Tensor` 一致：矩阵乘（`@`）、转置 \((\cdot)^{\top}\)、`softmax`、`tril`、`triu`、`masked_fill`、切片 `[start:stop]`、堆叠 \([i<n]\,f(i)\)、拼接 \(\mathbin{+\mkern-4mu+}\)。提升到 `Tensor ℝ* s` 即在超实数上解释条目。形状 cast 相等记为 \(\simeq\)（`SEq`）。

**`band_part`（非 PyTorch 原生 API）。** PyTorch 无 `band_part`。本库命名 TensorFlow 算子 [`tf.linalg.band_part`](https://tensorflow.google.cn/api_docs/python/tf/linalg/band_part)，用 PyTorch 原语定义：

```python
# matches Tensor.band_part in special.lean (d=1: no extra masked_fill)
def band_part(X, l, u, d=1):
    Y = (X.tril(u).triu(-l))
    if d == 1:
        return Y
    delta = j - i   # diagonal index on the last two axes
    return Y.masked_fill((delta + l) % d != 0, 0)
```

此处 `j - i` 为最后两轴上的对角指标 \(j-i\)（见 `sympy/matrices/expressions/special.lean`）。保留 \((i,j)\) 当且仅当 \(j-i\in[-l,u]\)；当 \(d>1\) 时还要求 \(d\mid(j-i+l)\)（dilated band；默认 \(d=1\)）。引理 `Tensor.BandPart.eq.Stack_BoolIn_Icc` 证明 \(d=1\) 时这等于 \(j-i\in[-l,u]\) 的布尔示性。记 \(\operatorname{band\_part}(l,u)\) 为 `band_part(ones(n,n), l, u)`。

*勿混淆* band 参数 \((l,u)\) 与下文*滑动窗口宽度* \(\ell\)：因果窗口 mask 用 \(\operatorname{band\_part}(\ell-1,0)\)，每行恰保留最近 \(\ell\) 个 key（\(j-i\in[1-\ell,0]\)）。

固定滑动窗口宽度 \(\ell\ge 1\)（每个 query 可 attend 的过去 key 数）、嵌入维 \(d_z\)，以及序列

\[
Q,K,V:\mathbb{N}\to\operatorname{Tensor}\mathbb{R}[d_z],
\]

及前缀输出 \(Z(n)\in\operatorname{Tensor}\mathbb{R}[n,d_z]\)。记 \(Q_{:n}=[i<n]\,Q(i)\)，\(K,V\) 同理。*记号：* \(\ell\) 为数学符号；Lean 与代码同名 `l`（\(\ell=\texttt{l}\)）。定理中 `band_part` mask 为 `band_part(..., l-1, 0)`，*不是* `band_part(..., l, 0)`——`band_part` 的第一个参数是 band 限，不是窗口宽度。

## 3.2 超实数 closeness \(\approx\)

**定义 3.1**（\(\mathbb{R}^*\) 上的 \(\approx\)，[`Hyperreal.XEq.is.InfinitesimalDivAbsSub`](http://www.lemma.cn/lean/?module=Hyperreal.XEq.is.InfinitesimalDivAbsSub)）。对 \(a,b\in\mathbb{R}^*\)，

\[
a\approx b
\quad\Longleftrightarrow\quad
\frac{|a-b|}{|a|+|b|+1}\to 0,
\]

即相对差距为无穷小。张量上 \(\approx\) 为该标量关系的逐分量提升。

这*不是* Mathlib 的无穷接近（\(a-b\) 无穷小）。它 mimic [`torch.isclose`](https://docs.pytorch.org/docs/stable/generated/torch.isclose.html)：绝对容差 effectively 为 0（无穷小绝对误差可推出 \(\approx\)，反之不然）；相对容差为上式分式，分母 \(+1\) 保证零附近稳定。两个无穷大可相差无穷大仍 \(\approx\)，朴素 \(|a-b|\) 测试不允许。

证明中，\(\exp(A+(\Xi-1)\infty)\approx e^{A}\Xi\) 在实数上恒等不成立，在两者皆无穷时经典 NSA 无穷接近也不成立；作为 \(\approx\) 成立。

## 3.3 超实数 band-part 掩码

**引理 3.2**（Mask exponential，[`lemma_gpt`](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T) 相关）。令 \(\Xi_{ij}=\mathbf{1}_{[-\ell+1,0]}(j-i)\)，

\[
\exp\bigl(A_{ij}+(\Xi_{ij}-1)\infty\bigr)\approx e^{A_{ij}}\Xi_{ij}.
\]

在 \(\Xi\) 支撑上无穷项消失；支撑外 logit 为 \(-\infty\)，指数为无穷小 0。对该矩阵的 softmax 即滑动窗口因果 softmax，无需有限 clip 常数（**图 1**）。

**图 1** 超实数 `band_part` 掩码：禁止位置的 logit 趋于 \(-\infty\)；\(\exp\) 在滑动窗口外给出无穷小零。

\[
\Xi_{ij}=\mathbf{1}_{[-\ell+1,0]}(j-i),\qquad
\exp\bigl(A_{ij}+(\Xi_{ij}-1)\infty\bigr)\approx e^{A_{ij}}\Xi_{ij}.
\]

## 3.4 堆叠分解（引理 `gpt`）

引理 [`gpt`](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T) 将 batch 滑动窗口 masked attention 展开为逐 token 一行——KV cache 内部使用的行形式。全程 \(\ell\ge 1\) 为*滑动窗口宽度*：第 \(i\) 行 query attend 下标在 \([(i+1-\ell)_+,i+1)\) 的 key（至多 \(\ell\) 个，因果）。Lean 证明用参数 `l` \(=\ell\)，mask `band_part(l-1, 0)`。

**引理 3.3**（堆叠分解，滑动窗口 \(\ell\)，[`lemma_gpt`](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T)）。固定 \(\ell\ge 1\)。对 \(Q,K,V\in\operatorname{Tensor}\mathbb{R}[n,d_z]\)，

\[
\begin{align*}
&\operatorname{softmax}\!\left(
\frac{QK^{\top}}{\sqrt{d_z}}
+\bigl((1_{[n,n]}).\operatorname{band\_part}(\ell-1,0)-1\bigr)\infty
\right)V \\
&\qquad\approx\;
[i<n]\;
\operatorname{softmax}\!\left(\frac{Q[i]\,K[(i+1-\ell):(i+1)]^{\top}}{\sqrt{d_z}}\right)
V[(i+1-\ell):(i+1)].
\end{align*}
\]

左式为宽度 \(\ell\) 的因果 band masked batch attention（mask \(\operatorname{band\_part}(\ell-1,0)\)）。右式逐行相同：第 \(i\) 行只 attend 长度 \(\ell\) 的 key/value 窗口——正是 decode 第 \(i\) 步 KV cache 拼接并复用的切片。当 \(\ell\ge n\) 时窗口为全前缀（经典 GPT 因果 attention）。

# 4 主结果

**定理 4.1**（KV cache 增量，[`lemma_kv_cache_lean`](http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T)）。设 \(\ell\ge 1\)，且对每个 \(n\)（式 (1)），

\[
Z(n)\;\approx\;
\operatorname{softmax}\!\left(
\frac{Q_{:n}K_{:n}^{\top}}{\sqrt{d_z}}
+\bigl((1_{[n,n]}).\operatorname{band\_part}(\ell-1,0)-1\bigr)\cdot\infty
\right)
V_{:n}.
\tag{1}
\]

mask 为 \(\operatorname{band\_part}(\ell-1,0)\)。在 PyTorch 中（`l` \(=\ell\) 为滑动窗口宽度）：

```python
# l == ell in the paper (sliding-window width; Lean name l)
torch.ones(n, n).tril(0).triu(-(l - 1))
```

等价于本库 `band_part(torch.ones(n, n), l - 1, 0)`。保留 \((i,j)\) 当且仅当 \(j-i\in[1-\ell,0]\)，即因果且只 attend 最近 \(\ell\) 个 key。

令

\[
\begin{align*}
K_w&=K_{:n}[(n+1-\ell):n],&
V_w&=V_{:n}[(n+1-\ell):n],\\
\operatorname{row}&=
\operatorname{softmax}\!\left(\frac{Q(n)\,(K_w^{\top}\mathbin{+\mkern-4mu+} K(n)^{\top})}{\sqrt{d_z}}\right)
(V_w\mathbin{+\mkern-4mu+}[V(n)]).
\end{align*}
\]

则（式 (2)）

\[
Z(n+1)\;\approx\; Z(n)\mathbin{+\mkern-4mu+}[\operatorname{row}].
\tag{2}
\]

故一个新 query 只 attend cache 窗口与新 key/value；前 \(n\) 行输出不变。

[SymPy 定理](http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache) 为全因果特例 `BandPart[n, 0]`，新行为

\[
\operatorname{softmax}\!\left(\frac{Q[n]\,[K[:n]^{\top}\mid K[n]]}{\sqrt{d_z}}\right)[V[:n]\mid V[n]],
\]

即窗口为整段前缀。Lean 中当 \(\ell>n+1\) 时，切片 \([(n+1-\ell):n]\) 为全前缀，可还原 SymPy 定理。

# 5 证明思路

证明在 Lean 4 单文件中完全检验，导入 §6.1 所列引理。**图 2** 概括 reduction。

**图 2** 定理 4.1 的证明 reduction。

\[
\begin{array}{c}
Z(n)\;\approx\;
\operatorname{softmax}\!\left(
\dfrac{Q_{:n}K_{:n}^{\top}}{\sqrt{d_{z}}}
+\bigl((1).\operatorname{band\_part}(\ell-1,0)-1\bigr)\infty
\right)V_{:n}
\quad(\forall n)
\\[1.1em]
\Big\downarrow\ \scriptstyle\text{在 }n+1\text{ 代入，引理 3.3}
\\[0.9em]
Z(n+1)\;\approx\;
[i<n+1]\;
\operatorname{softmax}\!\left(
\dfrac{Q[i]\,K[(i+1-\ell):(i+1)]^{\top}}{\sqrt{d_{z}}}
\right)
V[(i+1-\ell):(i+1)]
\\[1.1em]
\Big\downarrow\ \scriptstyle [i<n+1]f(i)=[i<n]f(i)\mathbin{+\mkern-4mu+}[i<1]f(n)
\\[0.9em]
\begin{array}{c@{\qquad}c}
[i<n]\,f(i) & [f(n)] \\[0.5em]
\Big\downarrow\ \scriptstyle h(n)+\text{引理 3.3} & \Big\downarrow\ \scriptstyle\text{slice}=\text{window}\mathbin{+\mkern-4mu+}\text{new token} \\[0.5em]
Z(n) &
\operatorname{softmax}\!\left(\dfrac{Q(n)\,(K_{w}^{\top}\mathbin{+\mkern-4mu+} K(n)^{\top})}{\sqrt{d_{z}}}\right)(V_{w}\mathbin{+\mkern-4mu+}[V(n)])
\end{array}
\\[1.6em]
Z(n+1)\;\approx\; Z(n)\mathbin{+\mkern-4mu+}[\operatorname{row}]
\end{array}
\]

**步骤 1：代入并展开。** 在 \(n+1\) 处应用假设 (1) 与引理 3.3，将 \(Z(n+1)\) 表为窗口行 attention 的堆叠。

**步骤 2：拆分堆叠。** 由 [`Tensor.Stack.eq.AppendStackS`](http://www.lemma.cn/lean/?module=Tensor.Stack.eq.AppendStackS)，对引理 3.3 的行函数 \(f\) 有 \([i<n+1]f(i)=[i<n]f(i)\mathbin{+\mkern-4mu+}[i<1]f(n)\)。\(\approx\) 在 \(\mathbin{+\mkern-4mu+}\) 下的相容性为 [`Tensor.XEqAppendS.of.XEq.XEq`](http://www.lemma.cn/lean/?module=Tensor.XEqAppendS.of.XEq.XEq)。

**步骤 3：识别前缀块。** 块 \([i<n]f(i)\) 由 \(n\) 处假设 (1) 与引理 3.3 等于 \(Z(n)\)；需证 \(K_{:n+1}\) 与 \(K_{:n}\) 在 \(n\) 以下窗口切片一致，用到 [`Tensor.SEqGetSliceSStack.of.LengthSlice`](http://www.lemma.cn/lean/?module=Tensor.SEqGetSliceSStack.of.LengthSlice) 与 [`Tensor.GetSliceStack.as.Stack_UFnAdd.of.Eq`](http://www.lemma.cn/lean/?module=Tensor.GetSliceStack.as.Stack_UFnAdd.of.Eq)。

**步骤 4：识别最后一行。** 单块 \([f(n)]\) 为 \(Q(n)\) 对 \(K_{:n+1}[(n+1-\ell):(n+1)]\simeq K_w\mathbin{+\mkern-4mu+}[K(n)]\)（\(V\) 同理）的 attention。拼接行块的转置在 shape cast 下为转置的拼接（[`Tensor.TAppend.as.AppendTS`](http://www.lemma.cn/lean/?module=Tensor.TAppend.as.AppendTS)）。与 softmax–scale–matmul 合成得 \(\operatorname{row}\)，即 (2)。

# 6 形式化工件

已完成陈述的交互可视化：

- SymPy：<http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache>
- Lean 4：<http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T>

SymPy 页展示 `apply` / `prove`：前缀相等推出与 `row` 拼接。Lean 页展示 `@[main] private lemma kv_cache`，含 `[NeZero (l : ℕ)]`、对 \(Z(n)\) 的全称假设、`let` 链 `Kn, Vn, Kw, Vw, KT, kT, row`，以及结论 \(Z(n+1)\approx Z(n)\mathbin{+\mkern-4mu+}[\operatorname{row}]\)。

源码：<https://github.com/math-proof/lemma>（Lean 4 在 `main`，SymPy 在 `master`）。

## 6.1 引理依赖

**图 3** 定理 4.1 的 Lean 证明主要导入引理（同文件 private 辅助引理未列出）。

- **[kv_cache](http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T)** — `Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T`
  - **[gpt](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T)** — `Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T`
    - [Stack_DotSoftmax](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax) — `Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax`
      - [Stack_BoolIn_Icc](http://www.lemma.cn/lean/?module=Tensor.BandPart.eq.Stack_BoolIn_Icc) — `Tensor.BandPart.eq.Stack_BoolIn_Icc`
      - [Mul_Stack_Bool](http://www.lemma.cn/lean/?module=Tensor.ExpAdd_MulInfty.eq.Mul_Stack_Bool) — `Tensor.ExpAdd_MulInfty.eq.Mul_Stack_Bool`
      - [DivExp_KeepdimSumExp](http://www.lemma.cn/lean/?module=Tensor.Softmax.eq.DivExp_KeepdimSumExp) — `Tensor.Softmax.eq.DivExp_KeepdimSumExp`
    - [Dot_Get](http://www.lemma.cn/lean/?module=Tensor.GetDot_TGetSlice.as.Dot_Get) — `Tensor.GetDot_TGetSlice.as.Dot_Get`
    - [DivGetSliceGet](http://www.lemma.cn/lean/?module=Tensor.GetSliceGetDiv.eq.DivGetSliceGet) — `Tensor.GetSliceGetDiv.eq.DivGetSliceGet`
  - [AppendStackS](http://www.lemma.cn/lean/?module=Tensor.Stack.eq.AppendStackS) — `Tensor.Stack.eq.AppendStackS`
  - [XEqAppendS](http://www.lemma.cn/lean/?module=Tensor.XEqAppendS.of.XEq.XEq) — `Tensor.XEqAppendS.of.XEq.XEq`
  - [Stack_UFnAdd](http://www.lemma.cn/lean/?module=Tensor.GetSliceStack.as.Stack_UFnAdd.of.Eq) — `Tensor.GetSliceStack.as.Stack_UFnAdd.of.Eq`
  - [LengthSlice](http://www.lemma.cn/lean/?module=Tensor.SEqGetSliceSStack.of.LengthSlice) — `Tensor.SEqGetSliceSStack.of.LengthSlice`
  - [SEqAppendS](http://www.lemma.cn/lean/?module=Tensor.SEqAppendS.of.SEq.SEq) — `Tensor.SEqAppendS.of.SEq.SEq`
  - [AppendTS](http://www.lemma.cn/lean/?module=Tensor.TAppend.as.AppendTS) — `Tensor.TAppend.as.AppendTS`

# 7 SymPy 与 Lean 4

SymPy 引理（2024-02-28，[`lemma_kv_cache_sympy`](http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache)）为全因果增量，用 `Equal` 而非 \(\approx\)；证明展开 Python `gpt`、代入 \(n\mapsto n+1\)、拆堆叠、将末行切片重写为 `SEq_Append`。

Lean 4 引理（2026-08-19，[`lemma_kv_cache_lean`](http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T)）保留 \(\ell\neq 0\)，切片 \([(n+1-\ell):n]\)，在 \(\mathbb{R}^*\) 上用 \(\approx\)，并含依赖转置 shape 所需的 `cast`。SymPy 侧有 batch 因果变体 [Tensor.Eq.of.Eq.gpt.kv_cache.batched](http://www.lemma.cn/py/?module=Tensor.Eq.of.Eq.gpt.kv_cache.batched)。

# 8 讨论与局限

本陈述是蕴涵，非充要：*已知* \(\forall n.\; Z(n)\approx\) masked-attention\((Q_{:n},K_{:n},V_{:n};\ell)\)，*则* \(Z(n+1)\approx Z(n)\mathbin{+\mkern-4mu+}[\operatorname{row}]\)。

它不构造神经网络中的 \(Q,K,V\)，不涉及多头或 GQA 布局，不证明 CUDA 级 bit 一致。它证明：在本 `Tensor` 演算中，KV cache 更新与滑动窗口 masked attention 的下一步是同一数学对象。

引理不估计窗口外 token 被丢弃的近似误差（mask 已编码）。它不替代 OrthoCache 的谱 eviction 定理或 TorchLean 的 kernel refinement 定理。互补表述：若前缀已是 exact masked attention，则 cache 单行更新即为长度 \(n+1\) 的 exact masked attention。

# 9 结论

我们给出一条可机器检验的恒等式，将 GPT 式 KV cache 更新与滑动窗口 masked attention 的增量一步对齐，并配套适用于 \(-\infty\) mask softmax 的超实数 closeness \(\approx\)。结果公开于 lemma.cn 与 GitHub，Lean 4 证明已检验，并有较早 SymPy 表述。后续工作包括多头布局、Lean batch 形式化，以及将 \(\approx\) 与浮点 refinement 定理衔接。

# 参考文献

与 `main.pdf` 参考文献表一致（arXiv 接收后在此补充 PDF 链接）。

1. OrthoCache authors. *OrthoCache: spectral eviction for KV caches*, 2025. Lean 4 formalization; public repository.
2. TorchLean authors. *TorchLean / BatchInvariantInference*, 2025. Schedule-explicit CUDA attention specification.
3. Hugging Face. [Cache explanation](https://huggingface.co/docs/transformers/en/cache_explanation), 2024.
4. Hugging Face. [DynamicCache](https://huggingface.co/docs/transformers/en/kv_cache), 2024.
5. Hugging Face. [Generation](https://huggingface.co/docs/transformers/en/main_classes/text_generation), 2024.
6. H. Jerome Keisler. *Elementary Calculus: An Infinitesimal Approach*, second edition. Prindle, Weber & Schmidt, 1986.
7. Woosuk Kwon et al. [vLLM: Easy, Fast, and Cheap LLM Serving](https://github.com/vllm-project/vllm), 2023.
8. math-proof. [kv_cache lemma (SymPy)](http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache), 2024.
9. math-proof. [Hyperreal.XEq.is.InfinitesimalDivAbsSub](http://www.lemma.cn/lean/?module=Hyperreal.XEq.is.InfinitesimalDivAbsSub), 2025.
10. math-proof. [Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T), 2025.
11. math-proof. [kv_cache lemma (Lean 4)](http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T), 2026.
12. math-proof. [lemma: machine-checked tensor calculus](https://github.com/math-proof/lemma), 2026.
13. Mathlib community. [Mathlib: Hyperreal numbers](https://leanprover-community.github.io/mathlib4_docs/), 2026.
14. PyTorch. [torch.isclose](https://docs.pytorch.org/docs/stable/generated/torch.isclose.html), 2024.
15. Alec Radford et al. *Language Models are Unsupervised Multitask Learners*. OpenAI Technical Report, 2019.
16. TensorFlow. [tf.linalg.band_part](https://tensorflow.google.cn/api_docs/python/tf/linalg/band_part), 2024.
17. Ashish Vaswani et al. *Attention Is All You Need*. NeurIPS, volume 30, 2017.
18. Lianmin Zheng et al. *SGLang: Efficient Execution of Structured Language Model Programs*, 2024.
