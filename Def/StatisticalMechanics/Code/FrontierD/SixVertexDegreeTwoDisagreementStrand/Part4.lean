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
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexTorusDartEdge
    (T : EvenTorus) (d : SixVertexTorusDart T) : SixVertexTorusEdge T :=
  sixVertexTorusIncidentEdge T d.1 d.2


def sixVertexTorusDartBondMate
    (T : EvenTorus) (d : SixVertexTorusDart T) : SixVertexTorusDart T :=
  ![((SixVertexArrows.cyclicPred T.width_pos d.1.1, d.1.2), (1 : Fin 4)),
    ((finitePeriodicSucc T.width_pos d.1.1, d.1.2), (0 : Fin 4)),
    ((d.1.1, SixVertexArrows.cyclicPred T.height_pos d.1.2), (3 : Fin 4)),
    ((d.1.1, finitePeriodicSucc T.height_pos d.1.2), (2 : Fin 4))] d.2

end
end StatMech.FrontierD
