import Lemma.Tensor.ItemGetGetSoftmaxAdd_Mul_Infty.eq.Ite
import Lemma.Hyperreal.Lt.of.XEqCoe.XEqCoe.Lt
import sympy.concrete.expr_with_limits
import sympy.Basic
import Lemma.Set.EqArgMax.of.All_Lt.In
open Tensor Hyperreal
set_option maxHeartbeats 2000000


/--
Argmax of a row of the hyperreal masked softmax versus argmax of the log-softmax row \( z \) stored at offsets \( \operatorname{off}(j) \):
if row \( i \) has a unique maximal logit \( a_{ij_0} \) among the unmasked entries, then the argmax of \( \operatorname{softmax}(a + ([P] - 1)\infty)_i \) is \( j_0 \), and the argmax of \( z \) over \( S \) is \( \operatorname{off}(j_0) \).
-/
@[main]
private lemma main
  {n : ℕ}
  [NeZero n]
-- given
  (P : Fin n → Fin n → Prop)
  [∀ i j, Decidable (P i j)]
  (a : Fin n → Fin n → ℝ)
  (i : Fin n)
  (zr : ℤ → ℝ)
  (off : Fin n → ℤ)
  (S : Set ℤ)
  (h_ne : ∀ i : Fin n, ∃ j : Fin n, P i j)
  (hS : ∀ j, P i j → off j ∈ S)
  (hz : ∀ j, P i j → zr (off j) = a i j - Real.log (∑ k ∈ Finset.univ.filter (fun k => P i k), Real.exp (a i k)))
  (huniq : ∃ j₀, P i j₀ ∧ ∀ j, P i j → (j ≠ j₀) → a i j < a i j₀)
  (hpad : ∀ o ∈ S, (¬ ∃ j, P i j ∧ off j = o) → ∀ j, P i j → (zr o < zr (off j))) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide (P i j)))
  let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (a i j : Tensor ℝ []) : Tensor ℝ [n, n])
  ∃ j₀, ArgMax Set.univ (fun j : Fin n => (((A + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []).item) = j₀ ∧ ArgMax S zr = off j₀ := by
-- proof
  intro Ξ A
  obtain ⟨j₀, hP₀, hmax⟩ := huniq
  have hD : ∀ j, P i j → 0 < ∑ k ∈ Finset.univ.filter (fun k => P i k), Real.exp (a i k) := fun j hj =>
    Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  have hD₀ := hD j₀ hP₀
  let w : Fin n → Fin n → ℝ := fun i j => Real.exp (a i j) / ∑ k ∈ Finset.univ.filter (fun k => P i k), Real.exp (a i k)
  have hitem : ∀ j : Fin n, (((A + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []).item ≈ (((if P i j then w i j else 0 : ℝ)) : ℝ*) :=
    fun j => ItemGetGetSoftmaxAdd_Mul_Infty.eq.Ite P a w h_ne (fun _ _ _ => rfl) i j
  have hw₀ : 0 < w i j₀ := div_pos (Real.exp_pos _) hD₀
  refine ⟨j₀, Set.EqArgMax.of.All_Lt.In (Set.mem_univ _) (fun j _ hj => ?_), Set.EqArgMax.of.All_Lt.In (hS j₀ hP₀) (fun o ho hne => ?_)⟩
  · have h₀ : (((A + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j₀, by simp [Tensor.length]⟩ : Tensor ℝ* []).item ≈ ((w i j₀ : ℝ) : ℝ*) := by
      simpa [hP₀] using hitem j₀
    refine Hyperreal.Lt.of.XEqCoe.XEqCoe.Lt (hitem j) h₀ ?_
    by_cases hPj : P i j
    · simp only [hPj, if_true]
      exact div_lt_div_of_pos_right (Real.exp_lt_exp.mpr (hmax j hPj hj)) hD₀
    · simp only [hPj, if_false]
      exact hw₀
  · by_cases hex : ∃ j, P i j ∧ off j = o
    · obtain ⟨j, hPj, rfl⟩ := hex
      have hj : j ≠ j₀ := fun e => hne (by rw [e])
      rw [hz j hPj, hz j₀ hP₀]
      linarith [hmax j hPj hj]
    · exact hpad o ho hex j₀ hP₀


-- created on 2026-10-01