/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Instance.StatisticalMechanics.Code.Ising.KWGeometricDual.Part3
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


def kwg_incidentMod2 {V : Type*} (v : V) : Sym2 V → Prop :=
  Sym2.lift ⟨fun x y => (x = v ∧ y ≠ v) ∨ (y = v ∧ x ≠ v), by
    intro x y
    apply propext
    constructor <;> rintro (h | h)
    · exact Or.inr ⟨h.1, h.2⟩
    · exact Or.inl ⟨h.1, h.2⟩
    · exact Or.inr ⟨h.1, h.2⟩
    · exact Or.inl ⟨h.1, h.2⟩⟩

end Ising
end StatMech
