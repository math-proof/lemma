module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.NearestSetGeometry.Part3
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


def translateSiteSet (a : Site d) (A : Set (Site d)) : Set (Site d) :=
  (fun x => a + x) '' A


end StatMech.FrontierA
