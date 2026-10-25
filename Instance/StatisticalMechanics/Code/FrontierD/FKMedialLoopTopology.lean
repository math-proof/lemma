/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable instance fkMedialLoopGraphDecidableRel
    (T : EvenTorus) (pairing : FKMedialLoopPairing T) :
    DecidableRel (fkMedialLoopGraph T pairing).Adj := Classical.decRel _

end StatMech.FrontierD
