/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part2
/-!
# Permutations and unsigned Stirling numbers

This file identifies unsigned Stirling numbers of the first kind with permutations having a
prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem decomposeFin_drop_step {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) (x : Fin (n + 1)) :
    e.SameCycle (dropFin q x)
      (dropFin q (Equiv.Perm.decomposeFin.symm (q.succ, e) x)) := by
  refine Fin.cases ?_ (fun a => ?_) x
  · change e.SameCycle q q
    exact Equiv.Perm.SameCycle.rfl
  · have hstep : e.SameCycle a (e a) := by
      exact Equiv.Perm.sameCycle_apply_right.mpr Equiv.Perm.SameCycle.rfl
    by_cases ha : e a = q
    · simpa [dropFin, ha] using hstep
    · rw [Equiv.Perm.decomposeFin_symm_apply_succ,
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) ((Fin.succ_injective n).ne ha)]
      exact hstep

theorem decomposeFin_sameCycle_drop {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) {x y : Fin (n + 1)}
    (hxy : (Equiv.Perm.decomposeFin.symm (q.succ, e)).SameCycle x y) :
    e.SameCycle (dropFin q x) (dropFin q y) := by
  let g := Equiv.Perm.decomposeFin.symm (q.succ, e)
  change g.SameCycle x y at hxy
  obtain ⟨m, hm⟩ := hxy.exists_nat_pow_eq
  have hpow (r : ℕ) : e.SameCycle (dropFin q x) (dropFin q ((g ^ r) x)) := by
    induction r with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ r ih =>
        exact Equiv.Perm.SameCycle.trans ih (by
          simpa [g, pow_succ'] using decomposeFin_drop_step q e ((g ^ r) x))
  simpa [hm] using hpow m

theorem decomposeFin_sameCycle_drop_succ {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) (x : Fin (n + 1)) :
    (Equiv.Perm.decomposeFin.symm (q.succ, e)).SameCycle x (dropFin q x).succ := by
  refine Fin.cases ?_ (fun a => ?_) x
  · refine ⟨1, ?_⟩
    simp [dropFin]
  · exact Equiv.Perm.SameCycle.rfl

theorem decomposeFin_sameCycle_iff {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) (x y : Fin (n + 1)) :
    (Equiv.Perm.decomposeFin.symm (q.succ, e)).SameCycle x y ↔
      e.SameCycle (dropFin q x) (dropFin q y) := by
  constructor
  · exact decomposeFin_sameCycle_drop q e
  · intro hxy
    exact Equiv.Perm.SameCycle.trans (decomposeFin_sameCycle_drop_succ q e x)
      (Equiv.Perm.SameCycle.trans (decomposeFin_sameCycle_lift q e hxy)
        (decomposeFin_sameCycle_drop_succ q e y).symm)

end MetaMathlibExt
