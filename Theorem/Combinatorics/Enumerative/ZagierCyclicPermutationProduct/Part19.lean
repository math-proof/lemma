/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part19
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagCutPos_mem {n : ℕ} (e π : Equiv.Perm (Fin n))
    (ε : Fin n) (hε : zagNontrivialAntiExceedance e π ε) :
    zagCutPos e π ε hε ∈ zagCutCandidates e π ε :=
  Finset.min'_mem _ _

theorem zagImage_lt_cutPos {n : ℕ} (e π : Equiv.Perm (Fin n))
    (ε : Fin n) (hε : zagNontrivialAntiExceedance e π ε) :
    e.symm (π ε) < zagCutPos e π ε hε := by
  classical
  have hm := zagCutPos_mem e π ε hε
  rw [zagCutCandidates] at hm
  exact (Finset.mem_filter.mp hm).2.1

theorem zagCutPos_path {n : ℕ} (e π : Equiv.Perm (Fin n))
    (ε : Fin n) (hε : zagNontrivialAntiExceedance e π ε) :
    ∃ t : ℕ, 0 < t ∧ t < zagCutHit e π ε ∧
      (π ^ t) (e (zagCycleMinPos e π ε)) = e (zagCutPos e π ε hε) := by
  classical
  have hm := zagCutPos_mem e π ε hε
  rw [zagCutCandidates] at hm
  exact (Finset.mem_filter.mp hm).2.2

theorem zagCutPos_min {n : ℕ} (e π : Equiv.Perm (Fin n))
    (ε : Fin n) (hε : zagNontrivialAntiExceedance e π ε)
    {i : Fin n} (hi : i ∈ zagCutCandidates e π ε) :
    zagCutPos e π ε hε ≤ i :=
  Finset.min'_le _ _ hi

theorem zagCutHit_no_return {n : ℕ} (e π : Equiv.Perm (Fin n))
    (ε : Fin n) {r : ℕ} (hr0 : 0 < r) (hrh : r < zagCutHit e π ε) :
    (π ^ r) (e (zagCycleMinPos e π ε)) ≠
      e (zagCycleMinPos e π ε) := by
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  let H := zagCutHit e π ε
  let hab : π.SameCycle a b := (zagCycleMinPos_mem e π ε).apply_right
  intro hreturn
  have hearly : (π ^ (H - r)) a = b := by
    calc
      (π ^ (H - r)) a = (π ^ (H - r)) ((π ^ r) a) := by rw [hreturn]
      _ = (π ^ ((H - r) + r)) a := by
        rw [pow_add, Equiv.Perm.mul_apply]
      _ = (π ^ H) a := by congr 2; omega
      _ = b := by simpa [a, b, H] using zagCutHit_spec e π ε
  have hmin : H ≤ H - r := by
    exact zagCycleHit_minimal π a b hab hearly
  omega

theorem zagCutAfterSwap_same_image {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    (π * Equiv.swap (e (zagCycleMinPos e π ε))
      (e (zagCutPos e π ε hε))).SameCycle
        (e (zagCycleMinPos e π ε)) (π ε) := by
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  let c := e (zagCutPos e π ε hε)
  let H := zagCutHit e π ε
  obtain ⟨t, ht0, htH, htc⟩ := zagCutPos_path e π ε hε
  have hac : (π ^ t) a = c := by simpa [a, c] using htc
  have hH : (π ^ H) a = b := by
    simpa [a, b, H] using zagCutHit_spec e π ε
  have htadd : t + (H - t) = H := by omega
  have hpath : ∀ r : ℕ, 0 < r → r ≤ H - t →
      ((π * Equiv.swap a c) ^ r) a = (π ^ (t + r)) a := by
    intro r hr0 hrd
    induction r using Nat.case_strong_induction_on with
    | hz => omega
    | hi r ih =>
        by_cases hrz : r = 0
        · subst r
          calc
            ((π * Equiv.swap a c) ^ (0 + 1)) a =
                (π * Equiv.swap a c) a := by simp
            _ = π c := by simp [Equiv.Perm.mul_apply]
            _ = π ((π ^ t) a) := by rw [hac]
            _ = (π ^ (t + (0 + 1))) a := by
              simpa only [Nat.zero_add, Equiv.Perm.mul_apply] using
                (congrArg (fun q : Equiv.Perm (Fin n) => q a)
                  (pow_succ' π t)).symm
        · have hr0' : 0 < r := Nat.pos_of_ne_zero hrz
          have hrd' : r ≤ H - t := by omega
          have ih' := ih r le_rfl hr0' hrd'
          have hjH : t + r < H := by omega
          have hja : (π ^ (t + r)) a ≠ a := by
            apply zagCutHit_no_return e π ε
            · omega
            · simpa [H] using hjH
          have hjc : (π ^ (t + r)) a ≠ c := by
            intro hjc
            have hperiod : (π ^ r) a = a := by
              apply (π ^ t).injective
              simpa [pow_add, Equiv.Perm.mul_apply, hac] using hjc
            exact zagCutHit_no_return e π ε hr0' (by omega) hperiod
          calc
            ((π * Equiv.swap a c) ^ (r + 1)) a =
                (π * Equiv.swap a c) (((π * Equiv.swap a c) ^ r) a) := by
              simpa only [Equiv.Perm.mul_apply] using
                congrArg (fun q : Equiv.Perm (Fin n) => q a)
                  (pow_succ' (π * Equiv.swap a c) r)
            _ = (π * Equiv.swap a c) ((π ^ (t + r)) a) := by rw [ih']
            _ = π ((π ^ (t + r)) a) := by
              rw [Equiv.Perm.mul_apply,
                Equiv.swap_apply_of_ne_of_ne hja hjc]
            _ = (π ^ (t + (r + 1))) a := by
              rw [show t + (r + 1) = (t + r) + 1 by omega]
              simpa only [Equiv.Perm.mul_apply] using
                (congrArg (fun q : Equiv.Perm (Fin n) => q a)
                  (pow_succ' π (t + r))).symm
  have hdpos : 0 < H - t := by omega
  refine ⟨((H - t : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, hpath (H - t) hdpos le_rfl, htadd, hH]

theorem zagNTAE_triangle_count {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    cycleQuotientCount
        (π * zagTriangle (e (zagCycleMinPos e π ε)) (π ε)
          (e (zagCutPos e π ε hε))) =
      cycleQuotientCount π + 2 := by
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  let c := e (zagCutPos e π ε hε)
  have habpos : e.symm a < e.symm b := by
    simpa [a, b] using zagNTAE_min_lt_image e π hε
  have hbcpos : e.symm b < e.symm c := by
    simpa [b, c] using zagImage_lt_cutPos e π ε hε
  have hac_ne : a ≠ c := fun h => by
    have := congrArg e.symm h
    omega
  have hab_ne : a ≠ b := fun h => by
    have := congrArg e.symm h
    omega
  have hac : π.SameCycle a c := by
    obtain ⟨t, _, _, ht⟩ := zagCutPos_path e π ε hε
    exact ⟨(t : ℤ), by simpa [a, c] using ht⟩
  exact zagCycleQuotientCount_mul_triangle π hac_ne hac hab_ne
    (by simpa [a, b, c] using zagCutAfterSwap_same_image e π ε hε)

end MetaMathlibExt
