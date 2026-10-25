/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeGraham
open Finset SimpleGraph


namespace StatMech.Ising

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

variable {V : Type*}


def threeBridgeSites (x y z : V) : Fin 3 -> V :=
  Fin.cases x (Fin.cases y (fun _ => z))

end
end StatMech.Ising
