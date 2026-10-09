import Lemma.Tensor.SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Ite_Block
import sympy.Basic
open Tensor


/--
Hyperreal masked softmax (py: `softmax(A + (Ξ - 1) * oo)` with the block mask `Ξ`): the masked entries are exactly `0`,
the unmasked ones carry the given weights, with every row having an unmasked entry.
-/
@[path]
private lemma bilinear_matrix_attention.biased.tf
  {n l u : ℕ}
  {d : ℕ}
  {Q K : Fin n → Fin d → ℝ}
  {W : Fin d → Fin d → ℝ}
  {H : Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h_l : 0 < l)
  (h_u : 0 < u)
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = ((∑ s, ∑ t, Q i s * W s t * K j t) + if i = j then H i else 0) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp ((∑ s, ∑ t, Q i s * W s t * K k t) + if i = k then H i else 0))) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)))
  let A : Tensor ℝ* [n, n] := ([i < n] [j < n] ((((∑ s, ∑ t, Q i s * W s t * K j t) + if i = j then H i else 0) : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
  (A + (Ξ - 1) * ∞).softmax ≈
    (([i < n] [j < n] (((if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) then Real.exp (z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))) else 0 : ℝ) : Tensor ℝ [])) : Tensor ℝ [n, n]) : Tensor ℝ* [n, n]) := by
-- proof
  exact SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Ite_Block.log (n := n) (m := n) (fun i j => ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)) (fun i j => (((∑ s, ∑ t, Q i s * W s t * K j t) + if i = j then H i else 0) : ℝ)) (fun i j => z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))) (fun i => ⟨i, by omega⟩) h


-- created on 2026-09-27
