import sympy.functions.elementary.integers
import sympy.tensor.functions
import sympy.tensor.stack


noncomputable def Tensor.rotaryMatrix' (θ : Tensor ℝ [d]) : Tensor ℝ [d + d, d + d] :=
  [i < d + d] [j < d + d]
    if (i : ℕ) is even then
      if (j : ℕ) = (i : ℕ) then
        (θ.cos[(i : ℕ) / 2]'(by grind) : Tensor ℝ [])
      else if (j : ℕ) = (i : ℕ) + 1 then
        -(θ.sin[(i : ℕ) / 2]'(by grind) : Tensor ℝ [])
      else
        (0 : Tensor ℝ [])
    else
      if (j : ℕ) = (i : ℕ) then
        (θ.cos[(i : ℕ) / 2]'(by grind) : Tensor ℝ [])
      else if (j : ℕ) + 1 = (i : ℕ) then
        (θ.sin[(i : ℕ) / 2]'(by grind) : Tensor ℝ [])
      else
        (0 : Tensor ℝ [])


/--
[RoFormer: Enhanced Transformer with Rotary Position Embedding](https://arxiv.org/pdf/2104.09864#page=5)

Su et al.'s original rotary matrix on interleaved pairs \((2i-1, 2i)\):

\[
{\boldsymbol{R}}^{d}_{\Theta,m}=\begin{pmatrix}
\cos m\theta_{1} & -\sin m\theta_{1} & 0 & 0 & \cdots & 0 & 0 \\
\sin m\theta_{1} & \cos m\theta_{1} & 0 & 0 & \cdots & 0 & 0 \\
0 & 0 & \cos m\theta_{2} & -\sin m\theta_{2} & \cdots & 0 & 0 \\
0 & 0 & \sin m\theta_{2} & \cos m\theta_{2} & \cdots & 0 & 0 \\
\vdots & \vdots & \vdots & \vdots & \ddots & \vdots & \vdots \\
0 & 0 & 0 & 0 & \cdots & \cos m\theta_{d/2} & -\sin m\theta_{d/2} \\
0 & 0 & 0 & 0 & \cdots & \sin m\theta_{d/2} & \cos m\theta_{d/2}
\end{pmatrix}
\]

Lean's $d$ is the half-dimension, so $\theta:\mathbb{R}^{d}$ plays the role of $(m\theta_{1},\ldots,m\theta_{d/2})$ and the matrix has shape $[d+d,d+d]$.
-/
@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d]) :
-- imply
  θ.rotaryMatrix' =
    [i < d + d] [j < d + d]
      if (i : ℕ) is even then
        if (j : ℕ) = (i : ℕ) then
          (θ.cos[(i : ℕ) / 2]'(by grind) : Tensor ℝ [])
        else if (j : ℕ) = (i : ℕ) + 1 then
          -(θ.sin[(i : ℕ) / 2]'(by grind) : Tensor ℝ [])
        else
          (0 : Tensor ℝ [])
      else
        if (j : ℕ) = (i : ℕ) then
          (θ.cos[(i : ℕ) / 2]'(by grind) : Tensor ℝ [])
        else if (j : ℕ) + 1 = (i : ℕ) then
          (θ.sin[(i : ℕ) / 2]'(by grind) : Tensor ℝ [])
        else
          (0 : Tensor ℝ []) :=
-- proof
  rfl


-- created on 2026-09-04
-- updated on 2026-09-05
