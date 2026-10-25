/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeGraham
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeActual
open Finset SimpleGraph


namespace StatMech.Ising

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

variable {V : Type*}


@[simp] theorem threeBridgeSites_zero (x y z : V) :
    threeBridgeSites x y z 0 = x := rfl

@[simp] theorem threeBridgeSites_one (x y z : V) :
    threeBridgeSites x y z 1 = y := rfl

@[simp] theorem threeBridgeSites_two (x y z : V) :
    threeBridgeSites x y z 2 = z := rfl


@[simp] theorem replicaBridgeInteraction_threeBridgeSites
    (x y z : V) (a b : ConfigSpace V) :
    replicaBridgeInteraction (threeBridgeSites x y z) a b =
      spin a x * spin b x + spin a y * spin b y + spin a z * spin b z := by
  simp [replicaBridgeInteraction, threeBridgeSites, Fin.sum_univ_succ]
  ring

end
end StatMech.Ising
