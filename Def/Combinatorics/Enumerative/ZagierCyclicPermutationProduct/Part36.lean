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
import Abbrev.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part5
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagPointedConfigByEquivOddMarkedConfigBy
    (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    ZagPointedConfigBy n hn k l ≃ ZagOddMarkedConfigBy n hn k l where
  toFun p := by
    let q := (zagFullSlice p.1).out
    refine ⟨q, ?_, ?_, ?_⟩
    · have hbase := zagFullSlice_basePoint p.1
      have hpoint : zagBasePoint p.1.point = zagBasePoint ⟨0, hn⟩ := Fin.ext rfl
      rw [hpoint] at hbase
      exact hbase.trans p.2.1
    · simpa only [q, p.2.2.1] using zagFullSlice_cycleCount p.1
    · exact (congrArg cycleQuotientCount
        (zagFullSlice_diagonal p.1)).trans p.2.2.2
  invFun q := by
    let p := (zagFullMerge q.1).out
    have hs : (zagFullSlice p).out = q.1 := zagFullSlice_fullMerge q.1
    refine ⟨p, ?_, ?_, ?_⟩
    · have hbase := zagFullSlice_basePoint p
      have hpoint : zagBasePoint p.point = zagBasePoint ⟨0, hn⟩ := Fin.ext rfl
      rw [hpoint, hs] at hbase
      exact hbase.symm.trans q.2.1
    · have hcount := zagFullSlice_cycleCount p
      rw [hs] at hcount
      omega
    · have hdiag := zagFullSlice_diagonal p
      rw [hs] at hdiag
      exact (congrArg cycleQuotientCount hdiag.symm).trans q.2.2.2
  left_inv p := by
    apply Subtype.ext
    exact zagFullMerge_fullSlice p.1
  right_inv q := by
    apply Subtype.ext
    exact zagFullSlice_fullMerge q.1

end MetaMathlibExt
