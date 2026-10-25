/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateSymmetry.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateMerge
open MeasureTheory


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}


def isingSignNormalizeEquiv (mask : Site d) : Site d ≃ Site d where
  toFun := isingSignNormalize mask
  invFun := isingSignNormalize mask
  left_inv := isingSignNormalize_involutive mask
  right_inv := isingSignNormalize_involutive mask

end StatMech.FrontierA
