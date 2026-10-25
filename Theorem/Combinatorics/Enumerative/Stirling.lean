/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling
/-!
# Permutations and unsigned Stirling numbers

This file identifies unsigned Stirling numbers of the first kind with permutations having a
prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

/-- The quotient cycle count is the number of nontrivial cycles plus fixed points. -/
theorem cycleQuotientCount_eq {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    cycleQuotientCount σ =
      Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) := by
  rw [cycleQuotientCount, Nat.card_congr (cycleQuotientEquiv σ), Nat.card_sum,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp only [Equiv.Perm.cycleType_def, Multiset.card_map, Finset.card_def,
    Fintype.card_coe]
  omega

theorem decomposeFin_sameCycle_succ {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) (x : Fin n) :
    (Equiv.Perm.decomposeFin.symm (q.succ, e)).SameCycle x.succ (e x).succ := by
  by_cases hx : e x = q
  · refine ⟨2, ?_⟩
    simp [pow_two, hx]
  · refine ⟨1, ?_⟩
    simp only [zpow_one, Equiv.Perm.decomposeFin_symm_apply_succ]
    exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) ((Fin.succ_injective n).ne hx)

theorem decomposeFin_sameCycle_lift {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) {x y : Fin n} (hxy : e.SameCycle x y) :
    (Equiv.Perm.decomposeFin.symm (q.succ, e)).SameCycle x.succ y.succ := by
  obtain ⟨m, hm⟩ := hxy.exists_nat_pow_eq
  have hpow (r : ℕ) :
      (Equiv.Perm.decomposeFin.symm (q.succ, e)).SameCycle
        x.succ ((e ^ r) x).succ := by
    induction r with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ r ih =>
        exact Equiv.Perm.SameCycle.trans ih (by
          simpa [pow_succ'] using decomposeFin_sameCycle_succ q e ((e ^ r) x))
  simpa [hm] using hpow m

end MetaMathlibExt
