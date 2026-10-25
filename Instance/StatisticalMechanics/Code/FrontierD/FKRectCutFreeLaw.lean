/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigEventLaw.Part2
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


noncomputable instance instFintypeFKRectCutClosedConfig (R : FKRectTorus) :
    Fintype (FKRectCutClosedConfig R) := by
  unfold FKRectCutClosedConfig
  infer_instance


end
end StatMech.FrontierD
