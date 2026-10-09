import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Ite_Mul
import sympy.Basic
open Tensor
set_option maxHeartbeats 2000000


private lemma sc_ext {x y : ℝ} (h : x = y) : (x : Tensor ℝ []) = (y : Tensor ℝ []) := by rw [h]




/--
Gathered form of one row of a hyperreal masked softmax times a value matrix.
The unmasked entries \( \{ j : P_{ij} \} \) of row \( i \) are enumerated (injectively) by \( \operatorname{dm} : [0, k) \to [0, n) \)
(the hypothesis `h_sum` says that summing over the mask equals summing along \( \operatorname{dm} \)), and every row has an unmasked entry:
\[
\operatorname{softmax}(a + ([P] - 1)\infty)_i \, V_i \approx
\Bigl[ \sum_{t < k} \frac{e^{a_{i, \operatorname{dm}(t)}}}{\sum_{s < k} e^{a_{i, \operatorname{dm}(s)}}}\, v_{i, \operatorname{dm}(t), \ell} \Bigr]_\ell .
\]
-/
@[path]
private lemma main
  {n d k : ℕ}
-- given
  (P : Fin n → Fin n → Prop)
  [∀ i j, Decidable (P i j)]
  (a : Fin n → Fin n → ℝ)
  (v : Fin n → Fin n → Fin d → ℝ)
  (dm : Fin k → Fin n)
  (h_ne : ∀ i : Fin n, ∃ j : Fin n, P i j)
  (i : Fin n)
  (h_sum : ∀ g : Fin n → ℝ, ∑ j ∈ Finset.univ.filter (fun j => P i j), g j = ∑ t : Fin k, g (dm t)) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide (P i j)))
  let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (a i j : Tensor ℝ []) : Tensor ℝ [n, n])
  let Vᵢ : Tensor ℝ [n, d] := [j < n] [l < d] (v i j l : Tensor ℝ [])
  ((A + (Ξ - 1) * ∞).softmax.get ⟨i, by grind⟩) @ (Vᵢ : Tensor ℝ* [n, d]) ≈
    ((([l < d] ((∑ t : Fin k, Real.exp (a i (dm t)) / (∑ s : Fin k, Real.exp (a i (dm s))) * v i (dm t) l : ℝ) : Tensor ℝ [])) : Tensor ℝ [d]) : Tensor ℝ* [d]) := by
-- proof
  intro Ξ A Vᵢ
  have h0 := DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Ite_Mul.row P a
    (fun i j => Real.exp (a i j) / ∑ k ∈ Finset.univ.filter (fun k => P i k), Real.exp (a i k)) v h_ne (fun i j hp => rfl) i
  refine h0.trans (Tensor.XEq.of.Eq ?_)
  congr 1
  congr 1
  funext l
  apply sc_ext
  have hS := h_sum (fun j => Real.exp (a i j))
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter, hS]
  rw [h_sum (fun j => Real.exp (a i j) / (∑ s : Fin k, Real.exp (a i (dm s))) * v i j l)]


-- created on 2026-10-01