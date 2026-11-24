module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Def.StatisticalMechanics.Code.Lattice.DartNext.Part3
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

theorem IsBoundaryDart.tail_mem {K : Set (Site 2)} {e : Dart}
    (h : IsBoundaryDart K e) : e.tail ∈ K := h.1

theorem IsBoundaryDart.head_not_mem {K : Set (Site 2)} {e : Dart}
    (h : IsBoundaryDart K e) : e.head ∉ K := h.2


end Lattice
end StatMech
