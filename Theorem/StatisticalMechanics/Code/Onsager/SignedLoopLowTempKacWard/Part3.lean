/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceClosure
import Def.StatisticalMechanics.Code.Onsager.SignedLoopLowTempKacWard.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

open StatMech.FrontierA

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

@[simp] theorem kwg_subdivWeight_central (x : E -> ℂ) (e : E) :
    (kwg_subdivWeight (V := V) x) (kwg_subdivCentralEdge e) = x e := by
  unfold kwg_subdivWeight
  split
  · rename_i h
    congr 1
    apply kwg_subdivCentralEdge_injective (V := V) (E := E)
    exact h.choose_spec
  · rename_i h
    exact (h ⟨e, rfl⟩).elim

@[simp] theorem kwg_subdivWeight_left (ends : E -> Sym2 V)
    (x : E -> ℂ) (e : E) :
    (kwg_subdivWeight (V := V) x) (kwg_subdivLeftEdge ends e) = 1 := by
  unfold kwg_subdivWeight
  rw [dif_neg]
  rintro ⟨e', heq⟩
  unfold kwg_subdivCentralEdge kwg_subdivLeftEdge at heq
  rw [Sym2.eq_iff] at heq
  rcases heq with h | h <;> simp at h

@[simp] theorem kwg_subdivWeight_right (ends : E -> Sym2 V)
    (x : E -> ℂ) (e : E) :
    (kwg_subdivWeight (V := V) x) (kwg_subdivRightEdge ends e) = 1 := by
  unfold kwg_subdivWeight
  rw [dif_neg]
  rintro ⟨e', heq⟩
  unfold kwg_subdivCentralEdge kwg_subdivRightEdge at heq
  rw [Sym2.eq_iff] at heq
  rcases heq with h | h <;> simp at h

theorem kwg_subdivGadget_owner_unique (ends : E -> Sym2 V)
    {e e' : E} {edge : kwg_SubdivEdge V E}
    (he : edge ∈ kwg_subdivGadgetEdges ends e)
    (he' : edge ∈ kwg_subdivGadgetEdges ends e') : e = e' := by
  simp only [kwg_subdivGadgetEdges, Finset.mem_insert,
    Finset.mem_singleton] at he he'
  rcases he with rfl | rfl | rfl <;> rcases he' with h | h | h
  · exact kwg_subdivLeftEdge_injective ends h
  · exfalso
    unfold kwg_subdivLeftEdge kwg_subdivCentralEdge at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h <;> simp at h
  · exfalso
    unfold kwg_subdivLeftEdge kwg_subdivRightEdge at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h <;> simp at h
  · exfalso
    unfold kwg_subdivCentralEdge kwg_subdivLeftEdge at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h <;> simp at h
  · exact kwg_subdivCentralEdge_injective h
  · exfalso
    unfold kwg_subdivCentralEdge kwg_subdivRightEdge at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h <;> simp at h
  · exfalso
    unfold kwg_subdivRightEdge kwg_subdivLeftEdge at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h <;> simp at h
  · exfalso
    unfold kwg_subdivRightEdge kwg_subdivCentralEdge at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h <;> simp at h
  · exact kwg_subdivRightEdge_injective ends h

theorem kwg_subdivGadgets_pairwiseDisjoint (ends : E -> Sym2 V)
    (F : Finset E) :
    (↑F : Set E).PairwiseDisjoint (kwg_subdivGadgetEdges ends) := by
  intro e _ e' _ hne
  change Disjoint (kwg_subdivGadgetEdges ends e)
    (kwg_subdivGadgetEdges ends e')
  rw [Finset.disjoint_left]
  intro edge he he'
  exact hne (kwg_subdivGadget_owner_unique ends he he')

theorem kwg_subdivLift_weight_product (ends : E -> Sym2 V)
    (x : E -> ℂ) (F : Finset E) :
    ∏ edge ∈ kwg_subdivLift ends F, kwg_subdivWeight (V := V) x edge =
      ∏ e ∈ F, x e := by
  unfold kwg_subdivLift
  rw [Finset.prod_biUnion (kwg_subdivGadgets_pairwiseDisjoint ends F)]
  apply Finset.prod_congr rfl
  intro e _
  unfold kwg_subdivGadgetEdges
  rw [Finset.prod_insert (by
      simp [kwg_subdivLeftEdge, kwg_subdivCentralEdge,
        kwg_subdivRightEdge, Sym2.eq_iff]),
    Finset.prod_insert (by
      simp [kwg_subdivCentralEdge, kwg_subdivRightEdge, Sym2.eq_iff]),
    Finset.prod_singleton]
  simp


end
end StatMech.Onsager
