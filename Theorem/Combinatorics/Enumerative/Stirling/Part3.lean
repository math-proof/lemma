/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part3
/-!
# Permutations and unsigned Stirling numbers

This file identifies unsigned Stirling numbers of the first kind with permutations having a
prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem decomposeFin_zero_pow_succ {n m : ℕ} (e : Equiv.Perm (Fin n))
    (x : Fin n) :
    ((Equiv.Perm.decomposeFin.symm (0, e)) ^ m) x.succ = ((e ^ m) x).succ := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply,
        Equiv.Perm.decomposeFin_symm_apply_succ]
      simp

theorem decomposeFin_zero_sameCycle_succ_iff {n : ℕ}
    (e : Equiv.Perm (Fin n)) (x y : Fin n) :
    (Equiv.Perm.decomposeFin.symm (0, e)).SameCycle x.succ y.succ ↔
      e.SameCycle x y := by
  constructor
  · intro hxy
    obtain ⟨m, hm⟩ := hxy.exists_nat_pow_eq
    refine ⟨(m : ℤ), ?_⟩
    rw [zpow_natCast]
    exact (Fin.succ_injective n) (by simpa [decomposeFin_zero_pow_succ] using hm)
  · intro hxy
    obtain ⟨m, hm⟩ := hxy.exists_nat_pow_eq
    refine ⟨(m : ℤ), ?_⟩
    rw [zpow_natCast, decomposeFin_zero_pow_succ, hm]

end MetaMathlibExt
