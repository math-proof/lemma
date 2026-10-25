/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCycleComplete.Part7
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def cycleCompleteSurfaceEquiv [Nonempty V]
    (hG : G.Preconnected) :
    {A : Finset G.edgeFinset //
        A ∈ gaugeClosedSurfaceFamily (cycleCompleteIncidence G hG)} ≃
      {delta : Finset (Sym2 V) // delta ∈ cutSpace G} where
  toFun A := ⟨cycleCompleteEdgeSet G A.1,
    (cycleComplete_isClosed_iff_mem_cutSpace G hG A.1).mp
      ((mem_cycleCompleteClosedFamily_iff G hG A.1).mp A.2)⟩
  invFun delta := ⟨cycleCompleteEdgePreimage G delta.1, by
    apply (mem_cycleCompleteClosedFamily_iff G hG _).mpr
    apply (cycleComplete_isClosed_iff_mem_cutSpace G hG _).mpr
    rw [cycleCompleteEdgeSet_preimage G]
    · exact delta.2
    · exact cutSpace_member_subset G delta.2⟩
  left_inv A := by
    apply Subtype.ext
    exact cycleCompleteEdgePreimage_set G A.1
  right_inv delta := by
    apply Subtype.ext
    apply cycleCompleteEdgeSet_preimage G
    exact cutSpace_member_subset G delta.2

end
end StatMech.FrontierA
