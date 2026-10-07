import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Image
import sympy.Basic
open Tensor


/--
py: `softmax(Q @ K.T / sqrt(d_z) + (Stack[i:n](Bool(i ∈ ⋃ {d[j]})) - Ones(n, n)) * oo) @ V = softmax(Q @ Stack[j:m](K[d[j]]).T / sqrt(d_z)) @ Stack[j:m](V[d[j]])`
in the hyperreal masked softmax, for logits \( A_{ij} \): the mask keeps exactly the \( m \) distinct columns \( d_j \), so
\[
\operatorname{softmax}(A + ([j \in \operatorname{im} d] - 1)\infty)\, V \approx
\Bigl[ \sum_{j < m} \frac{e^{A_{i, d_j}}}{\sum_{k < m} e^{A_{i, d_k}}}\, V_{d_j \ell} \Bigr]_{i\ell} .
\]
-/
@[main]
private lemma gather
  {n m d_z : ℕ}
  {d : Fin m → Fin n}
-- given
  (h₀ : (Finset.univ.image d).card = m)
  (h_m : 0 < m)
  (A : Fin n → Fin n → ℝ)
  (V : Fin n → Fin d_z → ℝ) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [_i < n] [j < n] (Bool.toNat (decide (j ∈ Finset.univ.image d)))
  let A' : Tensor ℝ* [n, n] := ([i < n] [j < n] (A i j : Tensor ℝ []) : Tensor ℝ [n, n])
  let V' : Tensor ℝ [n, d_z] := [j < n] [l < d_z] (V j l : Tensor ℝ [])
  (A' + (Ξ - 1) * ∞).softmax @ (V' : Tensor ℝ* [n, d_z]) ≈
    ((([i < n] [l < d_z] ((∑ j, Real.exp (A i (d j)) / (∑ k, Real.exp (A i (d k))) * V (d j) l : ℝ) : Tensor ℝ [])) : Tensor ℝ [n, d_z]) : Tensor ℝ* [n, d_z]) := by
-- proof
  exact DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Image h₀ h_m A V


/--
py (`position_representation.relative`): the same gather for \( \operatorname{softmax}\bigl(Q (K + K')^{\top} / \sqrt{d_z} + ([j \in \operatorname{im} d] - 1)\infty\bigr)(V + V') \):
\[
\operatorname{softmax}(A + ([j \in \operatorname{im} d] - 1)\infty)(V + V') \approx
\Bigl[ \sum_{j < m} \frac{e^{A_{i, d_j}}}{\sum_{k < m} e^{A_{i, d_k}}}\, (V + V')_{d_j \ell} \Bigr]_{i\ell},
\qquad A_{ij} = \frac{\sum_t Q_{it}(K_{jt} + K'_{jt})}{\sqrt{d_z}} .
\]
-/
@[main]
private lemma position_representation.relative.gather
  {n m d_z : ℕ}
  {d : Fin m → Fin n}
  {Q K K' V V' : Fin n → Fin d_z → ℝ}
-- given
  (h₀ : (Finset.univ.image d).card = m)
  (h_m : 0 < m) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [_i < n] [j < n] (Bool.toNat (decide (j ∈ Finset.univ.image d)))
  let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (((∑ t, Q i t * (K j t + K' j t)) / √(d_z : ℝ) : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
  let W : Tensor ℝ [n, d_z] := [j < n] [l < d_z] ((V j l + V' j l : ℝ) : Tensor ℝ [])
  (A + (Ξ - 1) * ∞).softmax @ (W : Tensor ℝ* [n, d_z]) ≈
    ((([i < n] [l < d_z] ((∑ j, Real.exp ((∑ t, Q i t * (K (d j) t + K' (d j) t)) / √(d_z : ℝ)) / (∑ k, Real.exp ((∑ t, Q i t * (K (d k) t + K' (d k) t)) / √(d_z : ℝ))) * (V (d j) l + V' (d j) l) : ℝ) : Tensor ℝ [])) : Tensor ℝ [n, d_z]) : Tensor ℝ* [n, d_z]) := by
-- proof
  exact DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Image h₀ h_m (fun i j => (∑ t, Q i t * (K j t + K' j t)) / √(d_z : ℝ)) (fun j l => V j l + V' j l)


-- created on 2022-01-09