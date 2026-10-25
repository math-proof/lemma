/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bctconnectedtree.Part3
import Theorem.StatisticalMechanics.Code.Walls.bskspanningtree.Part2
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


def bsk_ConnectedForestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∃ (V Leaf : Type) (_ : Fintype V) (_ : DecidableEq V) (_ : Nonempty V) (_ : Fintype Leaf)
    (_ : DecidableEq Leaf) (H : SimpleGraph V) (par : Leaf → V) (trifIdx : Site d → V)
    (compLeaf : Leaf → Set (Site d)),
    H.IsAcyclic ∧
    (∀ a : V, 3 ≤ (bsk_augG H par).degree (Sum.inl a)) ∧
    (∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
      btr_IsGenuineCoarseTrif ω L z → trifIdx y = trifIdx z → y = z) ∧
    (∀ l : Leaf, (compLeaf l ∩ vertexBoundary d R).Nonempty) ∧
    (∀ l l' : Leaf, l ≠ l' → Disjoint (compLeaf l) (compLeaf l'))


end StatMech.Walls
