/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
open scoped BigOperators
open Finset


namespace StatMech.Ising

open StatMech.Lattice

variable {d : ℕ}


def interfaceField (i : Fin d) : ConfigSpace (Site d) :=
  fun x => decide (0 ≤ x i)

end StatMech.Ising
