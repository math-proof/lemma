module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanStripInduction
open Set SimpleGraph MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


def jsi_cell (k r : ℤ) : Site 2 := ![k, r]

end Lattice
end StatMech
