module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Walls.jc10farupeven
public import Theorem.StatisticalMechanics.Code.Walls.jc10localconstancy
public import Theorem.StatisticalMechanics.Code.Walls.jc10cornerexists
public import Theorem.StatisticalMechanics.Code.Walls.jc10cornercellinK
public import Theorem.StatisticalMechanics.Code.Walls.jc10core
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def jc10core_topWallEdge (c : Site 2) (e : Sym2 (Site 2)) : Prop := by
  classical
  exact Sym2.lift ⟨fun x y =>
      (x 1 = y 1 ∧ x 1 = c 1) ∧
      ((x 0 = c 0 - 1 ∧ y 0 = c 0) ∨ (y 0 = c 0 - 1 ∧ x 0 = c 0)), by
    intro x y; simp only [eq_iff_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1.symm, h1 ▸ h2⟩, by tauto⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1.symm, h1 ▸ h2⟩, by tauto⟩⟩ e

end Walls
end StatMech
