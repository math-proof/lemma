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
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part27
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagSliceStep {n : ℕ} (p : ZagPointedPlane n) :
    ZagMarkedPlane n ⊕ ZagResidualMarkedPlane n := by
  classical
  let e' := zagSliceOrder p.order p.vertical p.point p.point_property
  let π' := zagSliceVertical p.order p.vertical p.point p.point_property
  exact if hres : zagNontrivialAntiExceedance e' π' p.point then
    Sum.inr {
      order := e'
      vertical := π'
      marked := zagSliceResidualTriple p.order p.vertical p.point
        p.point_property hres
      point := p.point
      point_property := hres
      point_cycle_min := zagSliceResidualTriple_third p.order p.vertical p.point
        p.point_property hres
    }
  else
    Sum.inl {
      order := e'
      vertical := π'
      marked := zagSliceTerminalTriple p.order p.vertical p.point
        p.point_property hres
    }

noncomputable def zagMergeStep {n : ℕ} :
    ZagMarkedPlane n ⊕ ZagResidualMarkedPlane n → ZagPointedPlane n
  | Sum.inl p => {
      order := zagMergeOrder p.order p.vertical p.marked
      vertical := zagMergeVertical p.order p.vertical p.marked
      point := zagMergePoint p.order p.vertical p.marked
      point_property := zagMergePoint_nontrivialAntiExceedance
        p.order p.vertical p.marked
    }
  | Sum.inr p => {
      order := zagResidualMergeOrder p.order p.vertical p.marked p.point
        p.point_property p.point_cycle_min
      vertical := zagResidualMergeVertical p.order p.vertical p.marked p.point
      point := p.point
      point_property := zagResidualMergePoint_nontrivialAntiExceedance
        p.order p.vertical p.marked p.point p.point_property p.point_cycle_min
    }

end MetaMathlibExt
