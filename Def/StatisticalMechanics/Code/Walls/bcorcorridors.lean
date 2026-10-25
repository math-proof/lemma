/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Walls.bcorcorridors
open Set SimpleGraph
open StatMech StatMech.Lattice


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option maxRecDepth 4000

set_option maxHeartbeats 800000


def bcor_Corridors (n : ℕ) (u₁ u₂ u₃ : Site 2) : Prop :=
  ∃ (P₁ : (hypercubicLattice 2).Walk ![0, 0] u₁)
    (P₂ : (hypercubicLattice 2).Walk ![0, 0] u₂)
    (P₃ : (hypercubicLattice 2).Walk ![0, 0] u₃),
      P₁.IsPath ∧ P₂.IsPath ∧ P₃.IsPath ∧
      (∀ z ∈ P₁.support, z ∈ box 2 n) ∧
      (∀ z ∈ P₂.support, z ∈ box 2 n) ∧
      (∀ z ∈ P₃.support, z ∈ box 2 n) ∧
      (∀ z, z ∈ P₁.support → z ∈ P₂.support → z = ![0, 0]) ∧
      (∀ z, z ∈ P₁.support → z ∈ P₃.support → z = ![0, 0]) ∧
      (∀ z, z ∈ P₂.support → z ∈ P₃.support → z = ![0, 0])


end StatMech.Walls
