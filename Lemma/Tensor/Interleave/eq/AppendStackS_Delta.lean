import sympy.functions.special.tensor_functions
import sympy.tensor.stack


def Tensor.interleave (d : ℕ) : Tensor ℝ [d + d, d + d] :=
  ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * i)) : Tensor ℝ [])) ++
    ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * i + 1)) : Tensor ℝ []))


/--
Even/odd gather sending interleaved pairs \((2i,\,2i+1)\) to split-half pairs \((i,\,i+d)\):

\[
{\boldsymbol{P}}=\begin{pmatrix}
1 & 0 & 0 & 0 & \cdots & 0 & 0 \\
0 & 0 & 1 & 0 & \cdots & 0 & 0 \\
\vdots & \vdots & \vdots & \vdots & \ddots & \vdots & \vdots \\
0 & 0 & 0 & 0 & \cdots & 1 & 0 \\
0 & 1 & 0 & 0 & \cdots & 0 & 0 \\
0 & 0 & 0 & 1 & \cdots & 0 & 0 \\
\vdots & \vdots & \vdots & \vdots & \ddots & \vdots & \vdots \\
0 & 0 & 0 & 0 & \cdots & 0 & 1
\end{pmatrix}
\]

So \(({\boldsymbol{P}}x)_{i}=x_{2i}\) and \(({\boldsymbol{P}}x)_{i+d}=x_{2i+1}\). Lean's $d$ is the half-dimension, and the matrix has shape $[d+d,d+d]$.
-/
@[main]
private lemma main
-- given
  (d : ℕ) :
-- imply
  Tensor.interleave d =
    ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * i)) : Tensor ℝ [])) ++
      ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * i + 1)) : Tensor ℝ [])) :=
-- proof
  rfl


-- created on 2026-09-04
-- updated on 2026-09-05
