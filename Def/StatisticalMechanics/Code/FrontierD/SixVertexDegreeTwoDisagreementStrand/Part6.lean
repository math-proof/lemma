module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
public import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part4
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoLocalMate
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    SixVertexDisagreementDart omega eta :=
  let sides := sixVertexLocalDisagreementSides
    (sixVertexLocalIncomingPattern omega d.1.1)
    (sixVertexLocalIncomingPattern eta d.1.1)
  let hcard : sides.card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree d
  let hd : d.1.2 ∈ sides := sixVertexDisagreementDart_side_mem d
  let other := finsetOther sides d.1.2 hcard hd
  ⟨(d.1.1, other), by
    change sixVertexTorusEdgeDisagrees omega eta
      (sixVertexTorusIncidentEdge T d.1.1 other)
    rw [← sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
    exact (mem_sixVertexLocalDisagreementSides _ _ other).mp
      (finsetOther_mem sides d.1.2 hcard hd)⟩

end
end StatMech.FrontierD
