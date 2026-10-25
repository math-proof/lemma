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
import Instance.StatisticalMechanics.Code.Ising.KWClosedWalkParity
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section EvenSubgraphDecomp

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

theorem degree_subgraphF_eq_incCount (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag) (v : V) :
    (subgraphF F).degree v = incCount F v := by
  classical
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  unfold incCount subgraphF
  apply Finset.card_bij (fun e _ => e)
  · intro e he
    rw [SimpleGraph.mem_incidenceFinset] at he
    have hmem : e ∈ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).edgeSet ∧ v ∈ e := he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at hmem
    rw [Finset.mem_filter]; exact ⟨hmem.1.1, hmem.2⟩
  · intro a _ b _ h; exact h
  · intro e he
    rw [Finset.mem_filter] at he
    refine ⟨e, ?_, rfl⟩
    rw [SimpleGraph.mem_incidenceFinset]
    have : e ∈ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).edgeSet ∧ v ∈ e := by
      refine ⟨?_, he.2⟩
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      exact ⟨Finset.mem_coe.mpr he.1, by rw [Sym2.mem_diagSet]; exact hF e he.1⟩
    exact this

theorem subgraphF_even (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hev : IsEvenSubgraph F) (v : V) : Even ((subgraphF F).degree v) := by
  rw [degree_subgraphF_eq_incCount F hF v]; exact hev v


end EvenSubgraphDecomp
end Ising
end StatMech
