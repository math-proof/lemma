/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDisagreementBondMate_involutive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (d : SixVertexDisagreementDart omega eta) :
    sixVertexDisagreementBondMate
        (sixVertexDisagreementBondMate d) = d := by
  apply Subtype.ext
  exact sixVertexTorusDartBondMate_involutive T d.1

theorem sixVertexDisagreementDart_side_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (d : SixVertexDisagreementDart omega eta) :
    d.1.2 ∈ sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega d.1.1)
      (sixVertexLocalIncomingPattern eta d.1.1) := by
  rw [mem_sixVertexLocalDisagreementSides,
    sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
  exact d.2

theorem sixVertexDisagreementDart_local_card_eq_two
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega d.1.1)
      (sixVertexLocalIncomingPattern eta d.1.1)).card = 2 := by
  rcases hdegree d.1.1 with hzero | htwo
  · have hmem := sixVertexDisagreementDart_side_mem d
    rw [Finset.card_eq_zero.mp hzero] at hmem
    exact False.elim (by simpa using hmem)
  · exact htwo


end
end StatMech.FrontierD
