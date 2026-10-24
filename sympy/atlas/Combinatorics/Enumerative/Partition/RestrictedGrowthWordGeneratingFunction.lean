/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RestrictedGrowthWordGeneratingFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Order
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Tactic.LinearCombination

/-! # Restricted-growth word multivariate generating function

This file proves the product formula for the multivariate generating function of
restricted-growth words with prescribed letter multiplicities.
-/

namespace MetaMathlibExt

private def rgwFrom (m : ℕ) {n k : ℕ} (u : Fin n → Fin k) : Prop :=
  ∀ i : Fin n, (u i : ℕ) ≤ m ∨ ∃ j : Fin n, j < i ∧ (u i : ℕ) ≤ (u j : ℕ) + 1

private noncomputable def rgwCount (k n m : ℕ) (e : Fin k → ℕ) : ℕ :=
  Nat.card {u : Fin n → Fin k //
    rgwFrom m u ∧ ∀ a : Fin k, Nat.card {i : Fin n // u i = a} = e a}

private def rgwSplitEquiv (k n : ℕ) :
    (Fin (n+1) → Fin k) ≃ Fin k × (Fin n → Fin k) where
  toFun u := (u 0, fun i => u i.succ)
  invFun := fun p => Fin.cons (α := fun _ => Fin k) p.1 p.2
  left_inv u := Fin.cons_self_tail u
  right_inv := by
    rintro ⟨a, w⟩
    refine Prod.ext ?_ ?_
    · change Fin.cons (α := fun _ => Fin k) a w 0 = a
      exact Fin.cons_zero _ _
    · change (fun i => Fin.cons (α := fun _ => Fin k) a w i.succ) = w
      funext i
      exact Fin.cons_succ _ _ i

private def rgwShift (k m : ℕ) (c : Fin k →₀ ℕ) : Fin k → ℕ :=
  fun a => c a + (if m ≤ (a : ℕ) then 1 else 0)

private noncomputable def rgwCoeff (k m : ℕ) (c : Fin k →₀ ℕ) : ℕ :=
  rgwCount k ((k - m) + c.sum (fun _ x => x)) m (rgwShift k m c)

private noncomputable def rgwSeries (k m : ℕ) : MvPowerSeries (Fin k) ℚ :=
  fun c => ((rgwCoeff k m c : ℕ) : ℚ)

private noncomputable def rgwPartialSum (k m : ℕ) : MvPowerSeries (Fin k) ℚ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < m), MvPowerSeries.X i
end MetaMathlibExt
