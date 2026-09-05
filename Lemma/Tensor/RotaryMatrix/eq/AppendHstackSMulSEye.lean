import sympy.matrices.expressions.special
import sympy.tensor.functions


noncomputable def Tensor.rotaryMatrix (θ : Tensor ℝ [d]) : Tensor ℝ [d + d, d + d] :=
  let I : Tensor ℝ [d, d] := Tensor.eye d
  (I * [_ < d] θ.cos).hstack (-(I * [_ < d] θ.sin)) ++ (I * [_ < d] θ.sin).hstack (I * [_ < d] θ.cos)


/--
[Utilities for Rotary Embedding](https://github.com/huggingface/transformers/blob/main/docs/source/en/internal/rope_utils.md)

Hugging Face Transformers' rotary matrix on half-dimension pairs \((i,\,i+d)\), as in `rotate_half`:

\[
{\boldsymbol{R}}^{d}_{\Theta,m}=\begin{pmatrix}
\cos m\theta_{1} & 0 & \cdots & 0 & -\sin m\theta_{1} & 0 & \cdots & 0 \\
0 & \cos m\theta_{2} & \cdots & 0 & 0 & -\sin m\theta_{2} & \cdots & 0 \\
\vdots & \vdots & \ddots & \vdots & \vdots & \vdots & \ddots & \vdots \\
0 & 0 & \cdots & \cos m\theta_{d/2} & 0 & 0 & \cdots & -\sin m\theta_{d/2} \\
\sin m\theta_{1} & 0 & \cdots & 0 & \cos m\theta_{1} & 0 & \cdots & 0 \\
0 & \sin m\theta_{2} & \cdots & 0 & 0 & \cos m\theta_{2} & \cdots & 0 \\
\vdots & \vdots & \ddots & \vdots & \vdots & \vdots & \ddots & \vdots \\
0 & 0 & \cdots & \sin m\theta_{d/2} & 0 & 0 & \cdots & \cos m\theta_{d/2}
\end{pmatrix}
\]

Lean's $d$ is the half-dimension, so $\theta:\mathbb{R}^{d}$ plays the role of $(m\theta_{1},\ldots,m\theta_{d/2})$ and the matrix has shape $[d+d,d+d]$.
-/
@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d]) :
-- imply
  θ.rotaryMatrix = (Tensor.eye d * [_ < d] θ.cos).hstack (-(Tensor.eye d * [_ < d] θ.sin)) ++ (Tensor.eye d * [_ < d] θ.sin).hstack (Tensor.eye d * [_ < d] θ.cos) :=
-- proof
  rfl


-- created on 2026-09-03
-- updated on 2026-09-05
