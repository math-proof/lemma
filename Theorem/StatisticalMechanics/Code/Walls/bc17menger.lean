/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc16menger.Part4
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Def.StatisticalMechanics.Code.Walls.bc17menger


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]


omit [DecidableEq V] in


theorem bc17_exists_finInj_of_le_ncard {s : Set V} (hs : s.Finite) {k : ℕ}
    (hk : k ≤ s.ncard) :
    ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, f i ∈ s := by
  classical
  rw [Set.ncard_eq_toFinset_card s hs] at hk
  obtain ⟨u, hu, hcard⟩ := Finset.exists_subset_card_eq hk
  refine ⟨fun i => (u.equivFin.symm (Fin.cast hcard.symm i) : V), ?_, ?_⟩
  · intro i j h
    have : u.equivFin.symm (Fin.cast hcard.symm i) = u.equivFin.symm (Fin.cast hcard.symm j) :=
      Subtype.ext h
    simpa [Fin.ext_iff] using (u.equivFin.symm.injective this)
  · intro i
    have hmem : (u.equivFin.symm (Fin.cast hcard.symm i) : V) ∈ u :=
      (u.equivFin.symm _).2
    exact hs.mem_toFinset.mp (hu hmem)


omit [DecidableEq V] in

theorem bc17_inter_isSeparator_bot (A B : Set V) :
    bc16_IsSeparator (⊥ : SimpleGraph V) A B (A ∩ B) := by
  intro s hs t ht p
  have hst : s = t := reachable_bot.mp p.reachable
  subst hst
  exact ⟨s, ⟨hs, ht⟩, p.start_mem_support⟩


end StatMech.Walls
