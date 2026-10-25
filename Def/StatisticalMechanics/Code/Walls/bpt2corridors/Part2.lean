/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bxpxpos.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Theorem.StatisticalMechanics.Code.Walls.bpt2corridors
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


def bpt2_ExtPred (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2)
    (ρ : ConfigSpace (Sym2 (Site 2))) : Prop :=
  ∃ S₁ S₂ S₃ : Set (Site 2),
    (a₁ ∈ S₁ ∧ a₂ ∈ S₂ ∧ a₃ ∈ S₃) ∧
    (x₁ ∈ S₁ ∧ x₂ ∈ S₂ ∧ x₃ ∈ S₃) ∧
    (Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃) ∧
    ((∀ u v : Site 2, s(u, v) ∈ I → u ∈ S₁ → v ∈ S₁) ∧
      (∀ u v : Site 2, s(u, v) ∈ I → u ∈ S₂ → v ∈ S₂) ∧
      (∀ u v : Site 2, s(u, v) ∈ I → u ∈ S₃ → v ∈ S₃)) ∧
    ((∀ u v : Site 2, u ∈ S₁ → IsOpenEdge 2 ρ u v → v ∈ S₁) ∧
      (∀ u v : Site 2, u ∈ S₂ → IsOpenEdge 2 ρ u v → v ∈ S₂) ∧
      (∀ u v : Site 2, u ∈ S₃ → IsOpenEdge 2 ρ u v → v ∈ S₃)) ∧
    ((cluster 2 ρ x₁).Infinite ∧ (cluster 2 ρ x₂).Infinite ∧ (cluster 2 ρ x₃).Infinite)


def bpt2_Ext (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | bpt2_ExtPred I a₁ a₂ a₃ x₁ x₂ x₃ (removeSite 0 (bpt2_closeI I ω))}


end StatMech.Walls
