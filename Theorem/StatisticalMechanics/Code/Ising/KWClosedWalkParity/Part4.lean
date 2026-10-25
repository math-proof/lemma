/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Def.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section EvenSubgraphDecomp

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

theorem subgraphF_adj (F : Finset (Sym2 V)) (a b : V) :
    (subgraphF F).Adj a b ↔ s(a,b) ∈ F ∧ a ≠ b := by
  unfold subgraphF; rw [SimpleGraph.fromEdgeSet_adj]; simp

theorem mem_edgeSet_subgraphF (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag) (e : Sym2 V) :
    e ∈ (subgraphF F).edgeSet ↔ e ∈ F := by
  unfold subgraphF
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · rintro ⟨h1, _⟩; exact Finset.mem_coe.mp h1
  · intro h; exact ⟨Finset.mem_coe.mpr h, by rw [Sym2.mem_diagSet]; exact hF e h⟩

end EvenSubgraphDecomp
end Ising
end StatMech
