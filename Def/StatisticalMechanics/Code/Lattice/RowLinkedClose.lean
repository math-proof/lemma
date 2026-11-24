module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
public import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

noncomputable def rlc_lexMeasure (M : ℤ) (z : Site 2) : ℕ :=
  (z 1 + M).toNat * (2 * M + 2).toNat + (z 0 + M).toNat


end Lattice
end StatMech
