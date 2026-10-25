/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateSymmetry.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateMerge
open MeasureTheory


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}


@[simp] theorem isingSignNormalize_involutive
    (mask x : Site d) :
    isingSignNormalize mask (isingSignNormalize mask x) = x := by
  funext a
  by_cases ha : mask a < 0 <;> simp [isingSignNormalize, ha]

end StatMech.FrontierA
