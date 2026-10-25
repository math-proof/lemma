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
import Structure.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part7
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagFullMergeCore {n : ℕ}
    (e π : Equiv.Perm (Fin n)) {root : Fin n}
    (marks : ZagOddMarks e π root) :
    ZagFullMergeResult ⟨e, π, root, marks⟩ := by
  classical
  cases marks with
  | terminal m =>
      let e' := zagMergeOrder e π m
      let π' := zagMergeVertical e π m
      let ε := zagMergePoint e π m
      let hε := zagMergePoint_nontrivialAntiExceedance e π m
      exact {
        out := ⟨e', π', ε, hε⟩
        root_eq := zagMerge_cycleMinPos e π m
        preserves_before := fun r hr hmem =>
          zagMerge_cycleMinPos_before e π m r hmem hr
      }
  | prepend _ middle third first_mem middle_mem first_lt_middle
      middle_lt_third tail =>
      let next := zagFullMergeCore e π tail
      have hfirst : root ∈
          zagCycleMinima next.out.order next.out.vertical := by
        apply next.preserves_before root
        · exact first_lt_middle.trans middle_lt_third
        · exact first_mem
      have hmiddle : middle ∈
          zagCycleMinima next.out.order next.out.vertical := by
        apply next.preserves_before middle middle_lt_third middle_mem
      have hthird : third ∈
          zagCycleMinima next.out.order next.out.vertical := by
        have hmem := zag_cycleMinPos_mem_cycleMinima next.out.order
          next.out.vertical next.out.point
        rwa [next.root_eq] at hmem
      let m : ZagMarkedTriple next.out.order next.out.vertical := {
        first := root
        middle := middle
        third := third
        first_mem := hfirst
        middle_mem := hmiddle
        third_mem := hthird
        first_lt_middle := first_lt_middle
        middle_lt_third := middle_lt_third
      }
      let e' := zagResidualMergeOrder next.out.order next.out.vertical m
        next.out.point next.out.point_property next.root_eq
      let π' := zagResidualMergeVertical next.out.order next.out.vertical m
        next.out.point
      let hε := zagResidualMergePoint_nontrivialAntiExceedance next.out.order
        next.out.vertical m next.out.point next.out.point_property next.root_eq
      exact {
        out := ⟨e', π', next.out.point, hε⟩
        root_eq := by
          simpa only [m] using
            zagResidualMerge_cycleMinPos next.out.order next.out.vertical
              m next.out.point next.out.point_property next.root_eq
        preserves_before := by
          intro r hr hmem
          apply zagResidualMerge_cycleMinPos_before next.out.order
            next.out.vertical m next.out.point r next.out.point_property
            next.root_eq
          · apply next.preserves_before r
            · exact hr.trans (first_lt_middle.trans middle_lt_third)
            · exact hmem
          · simpa only [m] using hr
      }
termination_by sizeOf marks

noncomputable def zagFullMerge {n : ℕ} (q : ZagOddMarkedPlane n) :
    ZagFullMergeResult q := by
  rcases q with ⟨e, π, root, marks⟩
  exact zagFullMergeCore e π marks

end MetaMathlibExt
