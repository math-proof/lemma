/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopLexUnitFineRelation
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSeedDisagreementComponentMask_selects_iff
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (seed e : SixVertexTorusEdge T) :
    sixVertexTorusMaskSelects
        (sixVertexSeedDisagreementComponentMask omega eta seed) e = true <->
      (sixVertexTorusDisagreementGraph omega eta).Reachable seed e := by
  classical
  rcases e with ⟨dir, v⟩
  fin_cases dir <;>
    simp [sixVertexTorusMaskSelects,
      sixVertexSeedDisagreementComponentMask]

theorem sixVertexSeedDisagreementComponentMask_full
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (seed : SixVertexTorusEdge T)
    (hseed : sixVertexTorusEdgeDisagrees omega eta seed) :
    SixVertexFullDisagreementMask omega eta
      (sixVertexSeedDisagreementComponentMask omega eta seed) := by
  let mask := sixVertexSeedDisagreementComponentMask omega eta seed
  constructor
  · intro v d hd
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
    apply sixVertexDisagreementGraph_reachable_disagrees hseed
    rw [sixVertexTorusLocalSwitchMask_apply] at hd
    exact (sixVertexSeedDisagreementComponentMask_selects_iff
      omega eta seed _).1 hd
  · intro v d r hd hr
    rw [sixVertexTorusLocalSwitchMask_apply] at hd ⊢
    rw [sixVertexSeedDisagreementComponentMask_selects_iff] at hd ⊢
    by_cases hdr : sixVertexTorusIncidentEdge T v d =
        sixVertexTorusIncidentEdge T v r
    · simpa [hdr] using hd
    · apply hd.trans
      apply SimpleGraph.Adj.reachable
      refine ⟨hdr, ?_, ?_, v, d, r, rfl, rfl⟩
      · exact sixVertexDisagreementGraph_reachable_disagrees hseed hd
      · exact (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
          omega eta v r).1 hr

end
end StatMech.FrontierD
