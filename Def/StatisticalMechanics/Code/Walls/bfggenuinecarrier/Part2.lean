/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfggenuinecarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bgtgenuineforest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bfggenuinecarrier
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bfg_GenuineExploration (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : Nonempty W) (_ : DecidableEq W)
    (G : SimpleGraph W) (_ : DecidableRel G.Adj) (ιT : Site d → W) (comp : W → Set (Site d)),
    G.IsAcyclic ∧ (∀ v, 1 ≤ G.degree v) ∧
    (∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → 3 ≤ G.degree (ιT y)) ∧
    (∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
      btr_IsGenuineCoarseTrif ω L z → ιT y = ιT z → y = z) ∧
    (∀ v, G.degree v = 1 → (comp v ∩ vertexBoundary d R).Nonempty) ∧
    (∀ u, G.degree u = 1 → ∀ v, G.degree v = 1 → u ≠ v → Disjoint (comp u) (comp v))


end StatMech.Walls
