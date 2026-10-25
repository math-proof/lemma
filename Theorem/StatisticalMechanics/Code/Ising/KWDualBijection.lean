/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section CycleSpace

variable {V : Type*} [DecidableEq V]


theorem incCount_symmDiff_mod_two (A B : Finset (Sym2 V)) (v : V) :
    incCount (symmDiff A B) v % 2 = (incCount A v + incCount B v) % 2 := by
  unfold incCount
  
  have hf : (symmDiff A B).filter (fun e => v ∈ e)
      = symmDiff (A.filter (fun e => v ∈ e)) (B.filter (fun e => v ∈ e)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto
  rw [hf]
  set FA := A.filter (fun e => v ∈ e)
  set FB := B.filter (fun e => v ∈ e)
  
  rw [symmDiff_def, Finset.sup_eq_union,
    Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  have h1 := Finset.card_inter_add_card_sdiff FA FB
  have h2 := Finset.card_inter_add_card_sdiff FB FA
  rw [Finset.inter_comm] at h2
  omega


theorem isEvenSubgraph_empty : IsEvenSubgraph (∅ : Finset (Sym2 V)) := by
  intro v; simp [incCount]


theorem isEvenSubgraph_symmDiff {A B : Finset (Sym2 V)}
    (hA : IsEvenSubgraph A) (hB : IsEvenSubgraph B) :
    IsEvenSubgraph (symmDiff A B) := by
  intro v
  rw [Nat.even_iff, incCount_symmDiff_mod_two]
  have ha := (Nat.even_iff).mp (hA v)
  have hb := (Nat.even_iff).mp (hB v)
  omega

end CycleSpace


section Transport

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in

theorem sym2map_injective (e : V ≃ W) : Function.Injective (Sym2.map e) := by
  intro x y h
  have h2 : Sym2.map e.symm (Sym2.map e x) = Sym2.map e.symm (Sym2.map e y) := by rw [h]
  rw [Sym2.map_map, Sym2.map_map, Equiv.symm_comp_self] at h2
  simpa using h2


end Transport
end Ising
end StatMech
