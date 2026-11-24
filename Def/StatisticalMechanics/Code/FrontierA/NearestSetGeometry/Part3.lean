module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.NearestSetGeometry.Part2
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


noncomputable def nearestSourceFinset (A B : Set (Site d)) : Finset (Site d) :=
  by
    classical
    exact if h : (nearestSourceSet A B).Finite then h.toFinset else ∅


end StatMech.FrontierA
