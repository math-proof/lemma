/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialUnitWindingSplitHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleExact
import Theorem.StatisticalMechanics.Code.FrontierD.PermSameCycleWeightSplit
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {T : EvenTorus}

instance fkMedialUnitWindingSplitHallPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p


end
end StatMech.FrontierD
