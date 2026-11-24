module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.StarHullWinding.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.WindingEarInduction.Part3
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

noncomputable def lmo_lexKey (z : Site 2) : ℤ ×ₗ ℤ := toLex (z 0, z 1)


end Lattice
end StatMech
