/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
open SimpleGraph Set


namespace StatMech

namespace Lattice

def jce_nbr (v : Site 2) : Fin 4 → Site 2
  | 0 => ![v 0 + 1, v 1]
  | 1 => ![v 0 - 1, v 1]
  | 2 => ![v 0, v 1 + 1]
  | 3 => ![v 0, v 1 - 1]


noncomputable def jce_degree (E : Set (Sym2 (Site 2))) (v : Site 2) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin 4 => s(v, jce_nbr v i) ∈ E)).card


def jce_ClosedContour (E : Set (Sym2 (Site 2))) : Prop :=
  ∀ v : Site 2, Even (jce_degree E v)


def jce_horizBelow (a b : ℤ) : Sym2 (Site 2) → Prop := by
  classical
  refine Sym2.lift ⟨fun x y =>
    (x 1 = y 1) ∧ (x 1 ≤ b) ∧ ((x 0 = a ∧ y 0 = a + 1) ∨ (x 0 = a + 1 ∧ y 0 = a)), ?_⟩
  intro x y; simp only [eq_iff_iff]
  constructor <;> (rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, h1 ▸ h2, by tauto⟩)

end Lattice
end StatMech
