module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.FiniteComplementConnected
public import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
open Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def arcns_OffSupportConnected (B : Set (Site 2)) : Prop :=
  ∀ x y : Site 2, x ∉ B → y ∉ B → (ffc_offSupportLattice B).Reachable x y


end Lattice
end StatMech
