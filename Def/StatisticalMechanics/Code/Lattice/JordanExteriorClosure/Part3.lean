/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part2
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box


def jec_wallEdge (z : Site 2) (e : Sym2 (Site 2)) : Prop := by
  classical
  exact Sym2.lift ⟨fun x y =>
      (x 1 = y 1 ∧ x 1 ≤ z 1 - 1) ∧
      ((x 0 = z 0 - 1 ∧ y 0 = z 0) ∨ (y 0 = z 0 - 1 ∧ x 0 = z 0)), by
    intro x y; simp only [eq_iff_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1.symm, h1 ▸ h2⟩, by tauto⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1.symm, h1 ▸ h2⟩, by tauto⟩⟩ e

end Lattice
end StatMech
