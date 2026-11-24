module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
public import Def.StatisticalMechanics.Code.Lattice.JordanExteriorClosure
open Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

open StatMech.RSW.Box


@[simp] theorem jec_mem_quad (z p : Site 2) :
    p ∈ jec_quad z ↔ p 0 ≤ z 0 - 1 ∧ p 1 ≤ z 1 - 1 := Iff.rfl


end Lattice
end StatMech
