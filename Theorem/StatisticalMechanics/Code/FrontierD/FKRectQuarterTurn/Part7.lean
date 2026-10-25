/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part7
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectQuarterTurnConfigurationEquiv_apply
    (R : FKRectTorus) (hheight : 4 < R.height)
    (omega : R.Configuration)
    (a : (fkRectQuarterTurnTorus R hheight).EdgeIndex) :
    fkRectQuarterTurnConfigurationEquiv R hheight omega a =
      omega ((fkRectQuarterTurnEdgeEquiv R hheight).symm a) := rfl


theorem fkRectOpenGraph_quarterTurn_adj
    (R : FKRectTorus) (hheight : 4 < R.height)
    (omega : R.Configuration) (x y : R.Vertex) :
    (fkRectOpenGraph (fkRectQuarterTurnTorus R hheight)
      (fkRectQuarterTurnConfigurationEquiv R hheight omega)).Adj
        (fkRectQuarterTurnVertexEquiv R hheight x)
        (fkRectQuarterTurnVertexEquiv R hheight y) ↔
      (fkRectOpenGraph R omega).Adj x y := by
  constructor
  · rintro ⟨a, haopen, ha⟩
    let b := (fkRectQuarterTurnEdgeEquiv R hheight).symm a
    refine ⟨b, ?_, ?_⟩
    · exact haopen
    · have hturn := fkRectTorusIndexedEdge_quarterTurn R hheight b
      rw [(fkRectQuarterTurnEdgeEquiv R hheight).apply_symm_apply a,
        ha] at hturn
      apply Sym2.map.injective
        (fkRectQuarterTurnVertexEquiv R hheight).injective
      simpa only [Sym2.map_mk] using hturn.symm
  · rintro ⟨a, haopen, ha⟩
    refine ⟨fkRectQuarterTurnEdgeEquiv R hheight a, ?_, ?_⟩
    · change omega ((fkRectQuarterTurnEdgeEquiv R hheight).symm
          (fkRectQuarterTurnEdgeEquiv R hheight a)) = true
      rw [(fkRectQuarterTurnEdgeEquiv R hheight).symm_apply_apply]
      exact haopen
    · rw [fkRectTorusIndexedEdge_quarterTurn, ha, Sym2.map_mk]


end
end StatMech.FrontierD
