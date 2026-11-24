module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.NearestSetGeometry
open Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Lattice

variable {d : ℕ}


def nearestSourceSet (A B : Set (Site d)) : Set (Site d) :=
  {x | x ∈ A ∧ ∃ y ∈ B, l1dist d x y = setL1Distance A B}

end StatMech.FrontierA
