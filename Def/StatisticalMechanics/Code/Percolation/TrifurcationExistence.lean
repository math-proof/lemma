/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.MengerCorridors.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


def tre_MergeFreeInsertion (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (R₁ R₂ R₃ : Set (Site d)),
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    (∀ e ∈ W, (0 : Site d) ∉ e) ∧
    (Connected d (removeSite 0 (forceOpenFinset W ω)) a₁ x₁ ∧
      Connected d (removeSite 0 (forceOpenFinset W ω)) a₂ x₂ ∧
      Connected d (removeSite 0 (forceOpenFinset W ω)) a₃ x₃) ∧
    ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧
      (cluster d (removeSite 0 ω) x₃).Infinite) ∧
    (a₁ ∈ R₁ ∧ a₂ ∈ R₂ ∧ a₃ ∈ R₃) ∧
    ((∀ u v, u ∈ R₁ → IsOpenEdge d ω u v → v ∈ R₁) ∧
      (∀ u v, u ∈ R₂ → IsOpenEdge d ω u v → v ∈ R₂) ∧
      (∀ u v, u ∈ R₃ → IsOpenEdge d ω u v → v ∈ R₃)) ∧
    ((∀ u v, u ∈ R₁ → s(u, v) ∈ W → v ∈ R₁) ∧
      (∀ u v, u ∈ R₂ → s(u, v) ∈ W → v ∈ R₂) ∧
      (∀ u v, u ∈ R₃ → s(u, v) ∈ W → v ∈ R₃)) ∧
    (Disjoint R₁ R₂ ∧ Disjoint R₁ R₃ ∧ Disjoint R₂ R₃)


end Percolation
end StatMech
