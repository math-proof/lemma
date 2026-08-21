# Formal KV Cache for GPT-Style Decoding

The same lemma is published on [lemma.cn](http://www.lemma.cn/) as two public visualizations that share the module family
`Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T`:

- **SymPy version** (interactive Python / symbolic exploration; lemma `kv_cache`):
  [http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache](http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache)
- **Lean 4 version** (machine-checked dependent type theory; lemma `kv_cache`):
  [http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T](http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T)

The [SymPy page](http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache) renders the original `apply` / `prove` statement as an interactive theorem document. The [Lean 4 page](http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T) renders the `@[main]` lemma with given/imply blocks, nested `let` binders, and hyperreal tensor equality \(\approx\). Both are the public faces of this result; the present note describes the mathematics that those pages display.

## Technical Field

The present disclosure belongs to formal tensor calculus for GPT-style autoregressive decoding: incremental inference of causal (and sliding-window) scaled dot-product attention, the mechanism implemented in production as a key–value (KV) cache. GPT-2/3/4 decode one token at a time; without a cache they would rebuild \(K,V\) over the whole prefix at every step. The lemma says that cache update is exactly one more row of the same masked attention.

It concerns an algebraic identity, not a numerical kernel. If every prefix \(Z(n)\) is the masked attention of the first \(n\) tokens, then \(Z(n+1)\) is exactly \(Z(n)\) concatenated with one new row computed from a window of cached keys and values plus the new token. The formula is stated twice in public: first as an interactive SymPy lemma on [lemma.cn/py](http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache) (created 2024-02-28), then as a Lean 4 lemma on [lemma.cn/lean](http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T) (2026-08-19), in a `Tensor` type semantically equivalent to `torch.Tensor`. The causal mask is \((\operatorname{band\_part}-1)\cdot\infty\) over the hyperreals \(\mathbb R^*\), so masked positions are identically zero after \(\exp\), rather than a floating-point stand-in such as \(-10^9\).

## Background

In a GPT decoder (GPT-2/3/4 and every Hugging Face `AutoModelForCausalLM`), each self-attention layer maps tokens to queries, keys, and values \(Q,K,V\). For the new token at position \(n\), causal attention is
\[
\operatorname{softmax}\!\left(\frac{q_n\,K_{:n+1}^\top}{\sqrt{d_z}}+M\right)V_{:n+1},
\]
where \(K_{:n+1}\) and \(V_{:n+1}\) are the keys and values of *all* tokens seen so far, and \(M\) hides future positions. The linear maps that produce \(K\) and \(V\) from hidden states do not depend on later tokens, so the first \(n\) key/value rows never change. Recomputing them at every generate step would be quadratic in the prefix length and is wasted work.

A **KV cache** stores those past keys and values and, at the next step, concatenates only the new pair:
\[
K_{:n+1}=K_{:n}\mathbin{++}[k_n],\qquad V_{:n+1}=V_{:n}\mathbin{++}[v_n].
\]
Hugging Face Transformers implements this as `use_cache=True` (the default in [`generate`](https://huggingface.co/docs/transformers/en/main_classes/text_generation)). The tensors travel as `past_key_values`; the default container is [`DynamicCache`](https://huggingface.co/docs/transformers/en/kv_cache), one \((K,V)\) pair per layer, shape growing as `[batch, heads, seq_len, head_dim]`. Internally the attention module concatenates the current \(k,v\) with the cache and attends with a mask of length `past_kv_length + 1`. Prefill still runs the full prompt once; decode then feeds **one new `input_id` per step** plus the cache, which is the loop `model(..., past_key_values=cache, use_cache=True)` in their [cache explanation](https://huggingface.co/docs/transformers/en/cache_explanation). Sliding-window models (and `DynamicCache` when `config` has a window) keep only the last \(\ell\) pairs, matching the Lean statement; vanilla GPT keeps the whole prefix, matching the SymPy statement.

That is an implementation. The lemma is the missing identity: if \(Z(n)\) is already the masked attention of the prefix, then Hugging Face’s “concat cache with the new \(k,v\) and take the last row” is exactly \(Z(n+1)\), not a different algorithm.

Public related work stops short of that identity.

- **PyTorch / Hugging Face / vLLM / SGLang** implement KV cache and sliding windows as runtime systems. Correctness is tested, not proved as a tensor equation.
- **Mathlib** has no `torch.Tensor` calculus, no `band_part`, and no softmax-attention lemmas.
- **OrthoCache** (Lean 4) machine-checks Parseval for the Walsh–Hadamard transform and a total-variation bound for *spectral eviction*. It does not prove that an incremental cached row equals full masked attention.
- **TorchLean / BatchInvariantInference** specifies schedule-explicit CUDA attention and batch invariance. That is a refinement of kernels against a denotation, not this library’s `Tensor` identity with `band_part` and hyperreal \(\infty\).
- **fak** (`model/kv`) reports bit-identical cache tests (\(\max|\Delta|=0\)) in Go against a native oracle. Those are empirical witnesses, not Lean/SymPy theorems.

The relation \(\approx\) used in the Lean statement is itself a major contribution of this library, and the present note had understated it. It is characterized by
[Hyperreal.XEq.is.InfinitesimalDivAbsSub](http://www.lemma.cn/lean/?module=Hyperreal.XEq.is.InfinitesimalDivAbsSub)
(created 2025-12-09):
\[
a\approx b
\quad\Longleftrightarrow\quad
\frac{|a-b|}{|a|+|b|+1}\to 0,
\]
i.e. the relative gap is infinitesimal. This is a formal `torch.isclose` on \(\mathbb R^*\): absolute tolerance is \(0\) (an infinitesimal absolute error already implies \(\approx\), but not conversely); relative tolerance is the displayed quotient, with \(+1\) in the denominator so the test is stable near zero. Two infinities may differ by an infinite amount and still be \(\approx\), which is exactly what a relative test must allow and what a naive \(|a-b|\) test forbids.

Public sources have **not** published this concept.

- **Keisler / classical NSA** and **Mathlib** (`Hyperreal.Infinitesimal`, deprecated `IsSt`) define “infinitely close” by \(a-b\) infinitesimal, equivalently \(\operatorname{st}(a)=\operatorname{st}(b)\) when both are finite. Infinite hyperreals have no standard part, so that relation is not a total closeness on \(\mathbb R^*\). Mathlib’s 2026 refactor replaces the predicates by `ArchimedeanClass` / `stdPart`; it still does not define a relative, `isclose`-style relation that compares two infinities.
- **`torch.isclose`** is IEEE floating-point code: \(\lvert x-y\rvert\le \mathrm{rtol}\cdot\lvert y\rvert+\mathrm{atol}\). Non-finite values are close iff they are equal. It is not a theorem, not hyperreal, and not proved equivalent to an infinitesimal relative error.
- **Coq / Isabelle NSA** developments follow the same \(a-b\) infinitesimal convention.

So the public record has (i) NSA infinitely-close for *finite* hyperreals and (ii) an unformalized float `isclose`. It does not have a machine-checked, total relation on \(\mathbb R^*\) that mimics `torch.isclose` with infinitesimal relative tolerance. The KV-cache lemma is one of the first large tensor identities that *uses* that relation: \(\exp(-\infty)\approx 0\), and masked softmax is \(\approx\) the windowed stack rather than definitionally equal in \(\mathbb R\).

This library already has the one-shot unfolding
[Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T)
(lemma `gpt`): masked attention of length \(n\) is the stack of \(n\) windowed row attentions
\[
\operatorname{softmax}\!\left(\frac{Q[i]\,K[(i+1-\ell):(i+1)]^\top}{\sqrt{d_z}}\right)V[(i+1-\ell):(i+1)].
\]
The KV-cache lemma’s distinct contribution is the *incremental* form of that unfolding: under the induction hypothesis that every prefix \(Z(n)\) equals full masked attention, one obtains
\[
Z(n+1)\approx Z(n)\mathbin{+\hspace{-0.35em}+}\operatorname{row}(q_n,K_w,k_n,V_w,v_n),
\]
with \(K_w,V_w\) the sliding window of width \(\ell\). The SymPy page proves the full-causal special case (window covering the whole prefix). The Lean 4 page proves the sliding-window statement with \(\ell\neq 0\), hyperreal \(\approx\), and explicit slice lengths. Among public Lean 4 sources, this is the first fully expanded torch-semantic identity of that kind. It is not the first mention of KV cache in Lean, and it is not a CUDA-kernel proof.

The two lemma.cn pages are the public visualizations of that statement.

## Summary

Fix a window width \(\ell\geq 1\) (`[NeZero (l : ℕ)]`), an embedding size \(d_z\), and sequences of vectors
\[
Q,K,V:\mathbb N\to\operatorname{Tensor}\mathbb R[d_z],
\]
together with prefix outputs \(Z(n)\in\operatorname{Tensor}\mathbb R[n,d_z]\). Write \(Q_{:n}=[i<n]\,Q(i)\) and likewise for \(K,V\). Write \(\approx\) for the library’s hyperreal closeness `XEq`, characterized by
[Hyperreal.XEq.is.InfinitesimalDivAbsSub](http://www.lemma.cn/lean/?module=Hyperreal.XEq.is.InfinitesimalDivAbsSub):
\[
a\approx b\;\Longleftrightarrow\; \bigl(|a-b|/(|a|+|b|+1)\bigr)\to 0.
\]
On tensors it is the pointwise lift of that scalar relation.

**Hypothesis.** For every \(n\),
\[
Z(n)\;\approx\;
\operatorname{softmax}\!\left(
\frac{Q_{:n}K_{:n}^\top}{\sqrt{d_z}}
+\bigl((1_{[n,n]}).\operatorname{band\_part}(\ell-1,0)-1\bigr)\cdot\infty
\right)
V_{:n}.
\]
The mask is PyTorch `torch.ones(n,n).band_part(l-1, 0)`: entry \((i,j)\) is kept if and only if \(j-i\in[1-\ell,0]\), i.e. causal attention restricted to the last \(\ell\) keys.

**Conclusion.** Let
\[
\begin{align*}
K_w&=K_{:n}[(n+1-\ell):n],&
V_w&=V_{:n}[(n+1-\ell):n],\\
\operatorname{row}&=
\operatorname{softmax}\!\left(\frac{Q(n)\,(K_w^\top\mathbin{+\hspace{-0.35em}+}K(n)^\top)}{\sqrt{d_z}}\right)
(V_w\mathbin{+\hspace{-0.35em}+}[V(n)]).
\end{align*}
\]
Then
\[
Z(n+1)\;\approx\; Z(n)\mathbin{+\hspace{-0.35em}+}[\operatorname{row}].
\]
Thus one new query attends only to the cached window plus the new key/value; the previous \(n\) output rows are reused unchanged.

The SymPy theorem is the same increment for the full-causal mask `BandPart[n, 0]`, with the new row
\[
\operatorname{softmax}\!\left(\frac{Q[n]\,[K[:n]^\top\mid K[n]]}{\sqrt{d_z}}\right)[V[:n]\mid V[n]],
\]
i.e. the special case in which the window is the entire prefix.

## Brief Description of the Drawings

FIG. 0 comprises the two public lemma.cn visualizations of the finished statement:

- SymPy: [http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache](http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache)
- Lean 4: [http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T](http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T)

FIG. 1 is the reduction used in the main theorem: instantiate the hypothesis at \(n+1\), unfold masked attention into a stack of windowed rows, split the stack as prefix \(++\) last row, and identify the two blocks with \(Z(n)\) and the cached `row`.

FIG. 2 is the import graph of major sub-lemmas used to prove the Lean theorem. Private helpers in the same file are absent (the lemma is proved in one file from imported Tensor lemmas). Links in FIG. 2 point to the Lean 4 pages; the SymPy counterpart of each module is the same path under `http://www.lemma.cn/py/?module=…`.

FIG. 3 is the hyperreal band-part mask: \((\Xi-1)\cdot\infty\) sends forbidden logits to \(-\infty\), and \(\exp\) of that is infinitesimally zero, so softmax is supported on the sliding window.

**FIG. 0 — public visualizations**

The [SymPy page](http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache) displays `apply` / `prove` for
\(\operatorname{Equal}(Z[:n],\operatorname{softmax}(\cdots)@V[:n])\)
implying
\(\operatorname{Equal}(Z[:n+1],[Z[:n],\operatorname{row}])\).
The [Lean 4 page](http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T) displays `@[main] private lemma kv_cache` with `[NeZero (l : ℕ)]`, the universal hypothesis on \(Z(n)\), the `let` chain `Kn, Vn, Kw, Vw, KT, kT, row`, and the conclusion \(Z(n+1)\approx Z(n)++[\operatorname{row}]\). Those two URLs are the public drawings of the lemma.

**FIG. 1 — reduction**

\[
\begin{array}{c}
Z(n)\;\approx\;
\operatorname{softmax}\!\left(
\dfrac{Q_{:n}K_{:n}^{\top}}{\sqrt{d_{z}}}
+\bigl((1).\operatorname{band\_part}(\ell-1,0)-1\bigr)\infty
\right)V_{:n}
\quad(\forall n)
\\[1.1em]
\Big\downarrow\ \scriptstyle\text{instantiate at }n+1,\ \text{lemma }gpt
\\[0.9em]
Z(n+1)\;\approx\;
[i<n+1]\;
\operatorname{softmax}\!\left(
\dfrac{Q[i]\,K[(i+1-\ell):(i+1)]^{\top}}{\sqrt{d_{z}}}
\right)
V[(i+1-\ell):(i+1)]
\\[1.1em]
\Big\downarrow\ \scriptstyle [i<n+1]f(i)=[i<n]f(i)\mathbin{++}[i<1]f(n)
\\[0.9em]
\begin{array}{c@{\qquad}c}
[i<n]\,f(i) & [f(n)] \\[0.5em]
\Big\downarrow\ \scriptstyle h(n)+gpt & \Big\downarrow\ \scriptstyle\text{slice }=\text{ window }++\text{ new token} \\[0.5em]
Z(n) &
\operatorname{softmax}\!\left(\dfrac{Q(n)\,(K_{w}^{\top}\mathbin{++}K(n)^{\top})}{\sqrt{d_{z}}}\right)(V_{w}\mathbin{++}[V(n)])
\end{array}
\\[1.6em]
Z(n+1)\;\approx\; Z(n)\mathbin{++}[\operatorname{row}]
\end{array}
\]

**FIG. 2 — lemma dependencies of the main theorem**

- `Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T` ([SymPy](http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache) / [Lean 4](http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T))
  - [Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T) — lemma `gpt`: masked \(n\times n\) attention equals the stack of windowed rows
    - [Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax) — general \((\ell,u)\)-band mask
      - [Tensor.BandPart.eq.Stack_BoolIn_Icc](http://www.lemma.cn/lean/?module=Tensor.BandPart.eq.Stack_BoolIn_Icc) — \(\operatorname{band\_part}(\ell,u)\) is the indicator of \(j-i\in[-\ell,u]\)
      - [Tensor.ExpAdd_MulInfty.eq.Mul_Stack_Bool](http://www.lemma.cn/lean/?module=Tensor.ExpAdd_MulInfty.eq.Mul_Stack_Bool) — \(\exp(A+(\Xi-1)\infty)\approx e^{A}\Xi\)
      - [Tensor.Softmax.eq.DivExp_KeepdimSumExp](http://www.lemma.cn/lean/?module=Tensor.Softmax.eq.DivExp_KeepdimSumExp)
    - [Tensor.GetDot_TGetSlice.as.Dot_Get](http://www.lemma.cn/lean/?module=Tensor.GetDot_TGetSlice.as.Dot_Get)
    - [Tensor.GetSliceGetDiv.eq.DivGetSliceGet](http://www.lemma.cn/lean/?module=Tensor.GetSliceGetDiv.eq.DivGetSliceGet)
  - [Tensor.Stack.eq.AppendStackS](http://www.lemma.cn/lean/?module=Tensor.Stack.eq.AppendStackS) — \([i<n+j]f(i)=[i<n]f(i)\mathbin{++}[i<j]f(n+i)\)
  - [Tensor.XEqAppendS.of.XEq.XEq](http://www.lemma.cn/lean/?module=Tensor.XEqAppendS.of.XEq.XEq) — \(\approx\) is congruent under `++`
  - [Tensor.GetSliceStack.as.Stack_UFnAdd.of.Eq](http://www.lemma.cn/lean/?module=Tensor.GetSliceStack.as.Stack_UFnAdd.of.Eq) — \(([i<n]f(i))[\mathrm{start}:\mathrm{stop}]\simeq [i<k]f(i+\mathrm{start})\)
  - [Tensor.SEqGetSliceSStack.of.LengthSlice](http://www.lemma.cn/lean/?module=Tensor.SEqGetSliceSStack.of.LengthSlice) — equal slice lengths give equal slices of two stacks
  - [Tensor.SEqAppendS.of.SEq.SEq](http://www.lemma.cn/lean/?module=Tensor.SEqAppendS.of.SEq.SEq)
  - [Tensor.TAppend.as.AppendTS](http://www.lemma.cn/lean/?module=Tensor.TAppend.as.AppendTS) — \((A\mathbin{++}B)^\top\simeq A^\top\mathbin{++}B^\top\) after the `cast` that swaps the first two axes

Related, not imported by this file: the batched causal cache
[Tensor.Eq.of.Eq.gpt.kv_cache.batched](http://www.lemma.cn/py/?module=Tensor.Eq.of.Eq.gpt.kv_cache.batched)
on the SymPy side.

**FIG. 3 — hyperreal band-part mask**

\[
\Xi_{ij}=\mathbf 1_{[-\ell+1,0]}(j-i),\qquad
\exp\bigl(A_{ij}+(\Xi_{ij}-1)\infty\bigr)\;\approx\; e^{A_{ij}}\Xi_{ij}.
\]
On the support of \(\Xi\), the infinite term vanishes and the logit is \(A_{ij}\). Off the support, the logit is \(-\infty\) and the exponential is infinitesimally \(0\). Softmax of that matrix is therefore exactly the sliding-window causal softmax, with no finite clip constant.

## Detailed Description

### 1. Tensors, hyperreals, and \(\approx\)

`Tensor ℝ s` is this library’s formalisation of a real tensor of shape `s`, with operations matching `torch.Tensor`: `matmul` (`@`), transpose \((\cdot)^\top\), `softmax`, `band_part`, slicing `[start:stop]`, stacking `[i < n] f i`, and concatenation `++`. Lifting to `Tensor ℝ* s` interprets entries in the hyperreals, so that \(\infty\) is a positive infinite scalar. Shape-cast equality is written \(\simeq\) (`SEq`).

The relation \(\approx\) (`XEq`) is **not** Mathlib’s “infinitely close” (\(a-b\) infinitesimal). It is the total closeness of
[Hyperreal.XEq.is.InfinitesimalDivAbsSub](http://www.lemma.cn/lean/?module=Hyperreal.XEq.is.InfinitesimalDivAbsSub), designed to mimic [`torch.isclose`](https://docs.pytorch.org/docs/stable/generated/torch.isclose.html):

- *atol.* Absolute error is \(\lvert a-b\rvert\). In \(\mathbb R^*\) one takes this as \(0\) in the finite-clip sense: if \(\lvert a-b\rvert\) is infinitesimal then \(a\approx b\), but the converse fails (two infinities can differ infinitely while remaining relatively close).
- *rtol.* Relative error is \(\lvert a-b\rvert/(\lvert a\rvert+\lvert b\rvert+1)\). The extra \(+1\) keeps the denominator away from \(0\). Two hyperreals are \(\approx\) iff this quantity is infinitesimal (\(\to 0\)).

That is the equality used throughout the KV-cache proof: \(\exp(A+(\Xi-1)\infty)\approx e^{A}\Xi\) is false as an identity of reals (the left-hand side is not even real), and false as NSA infinitely-close when both sides are infinite; it is true as `XEq`. Tensor \(\approx\) is this scalar relation on every entry.

The identity \((\sqrt{d_z})^2=d_z\) is not at issue here; \(\sqrt{d_z}\) is the usual attention scale, lifted as \(\sqrt{(d_z:\mathbb R^*)}\).

### 2. Masked attention as a stack of windows

Lemma `gpt` in
[Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T)
states: for \(Q,K,V\in\operatorname{Tensor}\mathbb R[n,d_z]\) and \(\ell\neq 0\),
\[
\begin{align*}
&\operatorname{softmax}\!\left(
\frac{QK^\top}{\sqrt{d_z}}
+\bigl((1_{[n,n]}).\operatorname{band\_part}(\ell-1,0)-1\bigr)\infty
\right)V \\
&\qquad\approx\;
[i<n]\;
\operatorname{softmax}\!\left(\frac{Q[i]\,K[(i+1-\ell):(i+1)]^\top}{\sqrt{d_z}}\right)
V[(i+1-\ell):(i+1)].
\end{align*}
\]
The left-hand side is the batched PyTorch form (`scores + causal_window_mask`, then `softmax @ V`). The right-hand side is the row-wise form used in a KV cache: row \(i\) attends only to keys and values in the half-open index interval \([(i+1-\ell)_+, i+1)\). The proof goes through
[Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax)
(FIG. 3) and then commutes slice, division, and transpose past the row index.

### 3. The induction hypothesis

The main lemma assumes the identity of §2 for *every* prefix length, with \(Z(n)\) as the name of that prefix output:
\[
\forall n,\quad
Z(n)\approx
\operatorname{softmax}\!\bigl(Q_{:n}K_{:n}^\top/\sqrt{d_z}+(\operatorname{band\_part}(\ell-1,0)-1)\infty\bigr)V_{:n}.
\]
In an implementation, \(Z(n)\) is the running decoder state of length \(n\). The hypothesis says that this state is not an ad-hoc cache invariant: it *is* full masked attention of the tokens seen so far.

### 4. Split the \((n+1)\)-stack

Instantiate the hypothesis at \(n+1\) and apply `gpt`. Then
[Tensor.Stack.eq.AppendStackS](http://www.lemma.cn/lean/?module=Tensor.Stack.eq.AppendStackS)
gives
\[
[i<n+1]\,f(i)\;=\;[i<n]\,f(i)\mathbin{++}[i<1]\,f(n),
\]
where \(f(i)\) is the windowed row attention of §2 at length \(n+1\). Congruence of \(\approx\) under `++` is
[Tensor.XEqAppendS.of.XEq.XEq](http://www.lemma.cn/lean/?module=Tensor.XEqAppendS.of.XEq.XEq).

The prefix block \([i<n]f(i)\) is identified with \(Z(n)\) by the hypothesis at \(n\), again via `gpt`, after proving that the window slices of \(K_{:n+1}\) and \(K_{:n}\) agree on indices below \(n\). That slice agreement is
[Tensor.SEqGetSliceSStack.of.LengthSlice](http://www.lemma.cn/lean/?module=Tensor.SEqGetSliceSStack.of.LengthSlice)
together with
[Tensor.GetSliceStack.as.Stack_UFnAdd.of.Eq](http://www.lemma.cn/lean/?module=Tensor.GetSliceStack.as.Stack_UFnAdd.of.Eq).

### 5. The last row is the cache update

The singleton block \([f(n)]\) is the attention of query \(Q(n)\) against keys \(K_{:n+1}[(n+1-\ell):(n+1)]\) and the corresponding values. That slice splits as
\[
K_{:n+1}[(n+1-\ell):(n+1)]
\;\simeq\;
K_{:n}[(n+1-\ell):n]\mathbin{++}[K(n)]
\;=\; K_w\mathbin{++}[K(n)],
\]
and likewise for \(V\). Transposing a concatenation of two row-blocks is concatenation of the two transposes, up to the shape `cast` that implements `List.EqSwap_0'1`:
[Tensor.TAppend.as.AppendTS](http://www.lemma.cn/lean/?module=Tensor.TAppend.as.AppendTS).
Composing with softmax-scale-matmul yields the `row` of the theorem statement. Therefore
\[
Z(n+1)\approx Z(n)\mathbin{++}[\operatorname{row}].
\]

### 6. SymPy versus Lean 4

The [SymPy lemma](http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache) (2024-02-28) is the full-causal increment: `BandPart[n, 0]`, new keys `[K[:n], K[n]]`, new values `[V[:n], V[n]]`, and `Equal` rather than \(\approx\). Its proof applies the Python `gpt` unfolding, substitutes \(n\mapsto n+1\), splits the stack, and rewrites the last-row slices as `SEq_Append`.

The [Lean 4 lemma](http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T) (2026-08-19) keeps a parameter \(\ell\neq 0\), slices \([(n+1-\ell):n]\), works in \(\mathbb R^*\) with \(\approx\), and carries the `cast`s required by dependent shapes of transpose. When \(\ell>n+1\), the slice \([(n+1-\ell):n]\) is the whole prefix (up to `min` in `List.LengthSlice`), recovering the SymPy theorem.

A batched causal variant lives at
[Tensor.Eq.of.Eq.gpt.kv_cache.batched](http://www.lemma.cn/py/?module=Tensor.Eq.of.Eq.gpt.kv_cache.batched).

### 7. Shape of the theorem

The statement is an implication, not an if-and-only-if:

- *given* \(\forall n.\; Z(n)\approx\text{masked-attention}(Q_{:n},K_{:n},V_{:n};\ell)\),
- *imply* \(Z(n+1)\approx Z(n)\mathbin{++}[\operatorname{row}]\).

It does not construct \(Q,K,V\) from a neural network, does not address multi-head or grouped-query layouts, and does not prove CUDA-level bit identity. Those are orthogonal. It does prove that, in the tensor calculus of this library, the KV-cache update is the same mathematical object as one more step of sliding-window masked attention.

### 8. What is not claimed

The lemma does not bound approximation error of dropping tokens outside the window (that is a modelling choice already present in the mask). It does not replace OrthoCache’s spectral eviction theorems or TorchLean’s kernel-refinement theorems. It is the complementary statement on `Tensor`: if prefixes are exact masked attention, then the cached one-row update is exact masked attention of length \(n+1\). That statement is the one visualized at
[lemma.cn/py](http://www.lemma.cn/py/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache)
and
[lemma.cn/lean](http://www.lemma.cn/lean/?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T).
