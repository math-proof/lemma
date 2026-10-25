/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeObstruction.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeActual
open Finset SimpleGraph


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*}


@[simp] theorem fourBridgeSites_zero (w x y z : V) :
    fourBridgeSites w x y z 0 = w := rfl

@[simp] theorem fourBridgeSites_one (w x y z : V) :
    fourBridgeSites w x y z 1 = x := rfl

@[simp] theorem fourBridgeSites_two (w x y z : V) :
    fourBridgeSites w x y z 2 = y := rfl

@[simp] theorem fourBridgeSites_three (w x y z : V) :
    fourBridgeSites w x y z 3 = z := rfl

end
end StatMech.Ising
