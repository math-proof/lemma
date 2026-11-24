module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
public import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def iwc_RightPocket : Set (Site 2) :=
  {z | (z 0 = 5 ∨ z 0 = 6) ∧ (z 1 = 1 ∨ z 1 = 2 ∨ z 1 = 3)}

end Lattice
end StatMech
