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
import Abbrev.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part7
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagPlaneConfigDiagonalEquivProduct
    (n k : ℕ) (hn : 0 < n) :
    ZagPlaneConfigDiagonal n hn k ≃
      ZagAnchoredOrder n hn ×
        {D : Equiv.Perm (Fin n) // cycleQuotientCount D = k} where
  toFun q := (q.1.1, ⟨zagDiagonal q.1.1.1 q.1.2, q.2⟩)
  invFun q := by
    refine ⟨(q.1, q.2.1⁻¹ * zagHorizontal q.1.1), ?_⟩
    have hdiag :
        zagDiagonal q.1.1 (q.2.1⁻¹ * zagHorizontal q.1.1) = q.2.1 := by
      simp only [zagDiagonal, mul_inv_rev, inv_inv]
      group
    rw [hdiag]
    exact q.2.2
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (zagDiagonal q.1.1.1 q.1.2)⁻¹ * zagHorizontal q.1.1.1 = q.1.2
      simp only [zagDiagonal, mul_inv_rev, inv_inv]
      group
  right_inv q := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change zagDiagonal q.1.1 (q.2.1⁻¹ * zagHorizontal q.1.1) = q.2.1
      simp only [zagDiagonal, mul_inv_rev, inv_inv]
      group

end MetaMathlibExt
