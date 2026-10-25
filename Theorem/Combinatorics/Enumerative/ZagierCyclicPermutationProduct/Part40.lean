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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part40
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagReverseOrder_reverseOrder {n : ℕ} (hn : 0 < n)
    (e : Equiv.Perm (Fin n)) :
    zagReverseOrder hn (zagReverseOrder hn e) = e := by
  let R := zagReverseIndex n hn
  have hR : R * R = 1 := by
    have hRinv : R⁻¹ = R := zagReverseIndex_inv hn
    calc
      R * R = R * R⁻¹ := congrArg (fun x => R * x) hRinv.symm
      _ = 1 := mul_inv_cancel R
  change (e * R) * R = e
  rw [mul_assoc, hR, mul_one]

theorem zagDiagonal_reflected {n : ℕ} (hn : 0 < n)
    (e π : Equiv.Perm (Fin n)) :
    zagDiagonal (zagReverseOrder hn e) (zagDiagonal e π)⁻¹ = π⁻¹ := by
  rw [zagDiagonal, zagHorizontal_reverseOrder, inv_inv, zagDiagonal]
  group

end MetaMathlibExt
