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
import Instance.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section EvenSubgraphDecomp

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

theorem compF_neighborSet_eq (F : Finset (Sym2 V)) {f a : V}
    (ha : (subgraphF F).Reachable f a) :
    (compF F f).neighborSet a = (subgraphF F).neighborSet a := by
  ext b; simp only [SimpleGraph.mem_neighborSet]
  constructor
  · rintro ⟨h, _, _⟩; exact h
  · intro h; exact ⟨h, ha, ha.trans h.reachable⟩

theorem compF_neighborSet_empty (F : Finset (Sym2 V)) {f a : V}
    (ha : ¬ (subgraphF F).Reachable f a) :
    (compF F f).neighborSet a = ∅ := by
  ext b; simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, hra, _⟩; exact ha hra

theorem compF_degree_even (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hev : IsEvenSubgraph F) (f a : V) : Even ((compF F f).degree a) := by
  classical
  by_cases ha : (subgraphF F).Reachable f a
  · rw [← SimpleGraph.card_neighborSet_eq_degree]
    have hcard : Fintype.card ((compF F f).neighborSet a) = (subgraphF F).degree a := by
      rw [← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_congr (Equiv.setCongr (compF_neighborSet_eq F ha))
    rw [hcard]; exact subgraphF_even F hF hev a
  · rw [← SimpleGraph.card_neighborSet_eq_degree]
    have hempty : (compF F f).neighborSet a = ∅ := compF_neighborSet_empty F ha
    have hcard : Fintype.card ((compF F f).neighborSet a) = 0 := by
      rw [Fintype.card_eq_zero_iff]; exact ⟨fun x => (hempty ▸ x.2 : (x:V) ∈ (∅:Set V))⟩
    rw [hcard]; exact Even.zero


end EvenSubgraphDecomp
end Ising
end StatMech
