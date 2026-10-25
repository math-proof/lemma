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
import Abbrev.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part10
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagPlanePairsEquivCyclePairs (n k : ℕ) :
    ZagPlanePairs n k ≃ ZagCyclePairs n k where
  toFun q := by
    refine ⟨(q.1.2 * q.1.1.1⁻¹, q.1.1.1), ?_, q.1.1.2, ?_⟩
    · have hfirst : q.1.2 * q.1.1.1⁻¹ =
          (q.1.1.1 * q.1.2⁻¹)⁻¹ := by
        simp only [mul_inv_rev, inv_inv]
      rw [hfirst, zagCycleQuotientCount_inv, q.2.2]
    · have hproduct : (q.1.2 * q.1.1.1⁻¹) * q.1.1.1 = q.1.2 := by group
      rw [hproduct, q.2.1]
  invFun p := by
    refine ⟨(⟨p.1.2, p.2.2.1⟩, p.1.1 * p.1.2), p.2.2.2, ?_⟩
    have hdiag : p.1.2 * (p.1.1 * p.1.2)⁻¹ = p.1.1⁻¹ := by
      simp only [mul_inv_rev]
      group
    rw [hdiag, zagCycleQuotientCount_inv, p.2.1]
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · group
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · group
    · rfl

noncomputable def zagPlaneConfigEquivCyclePairs
    (n k : ℕ) (hn : 0 < n) :
    ZagPlaneConfig n hn k ≃ ZagCyclePairs n k :=
  (zagPlaneConfigEquivPairs n k hn).trans (zagPlanePairsEquivCyclePairs n k)

end MetaMathlibExt
