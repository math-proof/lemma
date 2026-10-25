/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
open Set


namespace StatMech.FrontierA

open StatMech.Lattice

variable {d : ℕ}


def realizedL1Distances (A B : Set (Site d)) : Set ℕ :=
  {n | ∃ x ∈ A, ∃ y ∈ B, l1dist d x y = n}


noncomputable def setL1Distance (A B : Set (Site d)) : ℕ :=
  sInf (realizedL1Distances A B)


end StatMech.FrontierA
