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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part17
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagCutHit_spec {n : ℕ} (e π : Equiv.Perm (Fin n))
    (ε : Fin n) :
    (π ^ zagCutHit e π ε) (e (zagCycleMinPos e π ε)) = π ε :=
  zagCycleHit_spec π _ _ _

theorem zagCutHit_two_le {n : ℕ} (e π : Equiv.Perm (Fin n))
    {ε : Fin n} (hε : zagNontrivialAntiExceedance e π ε) :
    2 ≤ zagCutHit e π ε := by
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  have habpos := zagNTAE_min_lt_image e π hε
  have hbeps := zagNTAE_image_lt e π hε
  have hab_ne : a ≠ b := fun h => by
    apply (ne_of_lt habpos)
    exact e.injective (by simpa [a, b] using h)
  have hpos : 0 < zagCutHit e π ε :=
    zagCycleHit_pos π hab_ne _
  by_contra htwo
  have hone : zagCutHit e π ε = 1 := by omega
  have hp : π a = π ε := by
    simpa only [hone, pow_one, a] using zagCutHit_spec e π ε
  have haeps : a = ε := π.injective hp
  have : zagCycleMinPos e π ε = e.symm ε := by
    apply e.injective
    simpa [a] using haeps
  omega

theorem zagCutHit_pred {n : ℕ} (e π : Equiv.Perm (Fin n))
    {ε : Fin n} (hε : zagNontrivialAntiExceedance e π ε) :
    (π ^ (zagCutHit e π ε - 1)) (e (zagCycleMinPos e π ε)) = ε := by
  have htwo := zagCutHit_two_le e π hε
  have hs := zagCutHit_spec e π ε
  rw [show zagCutHit e π ε = zagCutHit e π ε - 1 + 1 by omega,
    pow_succ', Equiv.Perm.mul_apply] at hs
  exact π.injective hs

end MetaMathlibExt
