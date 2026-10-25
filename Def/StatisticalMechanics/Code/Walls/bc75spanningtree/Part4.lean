/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc74disjointforest.Part2
import Theorem.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc75spanningtree.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


open Classical in


def bc75_FiberGnTrifData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) : Prop :=
  ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type))
    (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S),
    (∀ y (hy : y ∈ bc73_fiber ω L R c),
      ∃ (v₁ v₂ v₃ : (↑S : Type))
        (h₁ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₁)
        (h₂ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₂)
        (h₃ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₃),
        ¬ (((bc75_fiberQuotBox ω L R c S).induce
              ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
            ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₁).symm⟩
            ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₂).symm⟩) ∧
        ¬ (((bc75_fiberQuotBox ω L R c S).induce
              ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
            ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₁).symm⟩
            ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₃).symm⟩) ∧
        ¬ (((bc75_fiberQuotBox ω L R c S).induce
              ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
            ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₂).symm⟩
            ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₃).symm⟩)) ∧
    (∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) ∧
    (∀ v : (↑S : Type), (bc75_spanForest ω L R c S).degree v = 1 → (v : Site d) ∈ vertexBoundary d R)


end StatMech.Walls
