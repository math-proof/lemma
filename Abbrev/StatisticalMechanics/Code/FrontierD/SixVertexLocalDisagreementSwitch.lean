/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexLocalIncomingPattern := Fin 4 -> Bool

end
end StatMech.FrontierD
