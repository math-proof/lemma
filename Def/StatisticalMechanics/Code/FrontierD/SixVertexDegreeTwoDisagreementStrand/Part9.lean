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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexTorusEdgeOutgoingDart
    {T : EvenTorus} (omega : SixVertexArrows T)
    (e : SixVertexTorusEdge T) : SixVertexTorusDart T :=
  if e.1 = 0 then
    if omega.horizontal e.2 then (e.2, (1 : Fin 4))
    else ((finitePeriodicSucc T.width_pos e.2.1, e.2.2), (0 : Fin 4))
  else
    if omega.vertical e.2 then (e.2, (3 : Fin 4))
    else ((e.2.1, finitePeriodicSucc T.height_pos e.2.2), (2 : Fin 4))

end
end StatMech.FrontierD
