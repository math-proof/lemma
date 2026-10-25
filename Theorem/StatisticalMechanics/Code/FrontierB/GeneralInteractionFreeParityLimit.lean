/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeSpinLimit.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousParityAvoidance.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity.Part3
import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeParityLimit
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Ising Lattice

theorem sym2_toFinset_map_embedding {V W : Type*}
    [DecidableEq V] [DecidableEq W] (f : V ↪ W) (e : Sym2 V) :
    (Sym2.map f e).toFinset = e.toFinset.map f := by
  ext y
  simp

theorem finset_map_symmDiff {V W : Type*}
    [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (A B : Finset V) :
    (A ∆ B).map f = A.map f ∆ B.map f := by
  ext y
  simp only [Finset.mem_map, Finset.mem_symmDiff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨hA, hB⟩ | ⟨hB, hA⟩
    · exact Or.inl ⟨⟨x, hA, rfl⟩,
        fun ⟨z, hz, heq⟩ => hB (by simpa [f.injective heq] using hz)⟩
    · exact Or.inr ⟨⟨x, hB, rfl⟩,
        fun ⟨z, hz, heq⟩ => hA (by simpa [f.injective heq] using hz)⟩
  · rintro (⟨⟨x, hA, rfl⟩, hB⟩ | ⟨⟨x, hB, rfl⟩, hA⟩)
    · exact ⟨x, Or.inl ⟨hA, fun hx => hB ⟨x, hx, rfl⟩⟩, rfl⟩
    · exact ⟨x, Or.inr ⟨hB, fun hx => hA ⟨x, hx, rfl⟩⟩, rfl⟩


theorem edgeBoundary_sym2FinsetMap {V W : Type*}
    [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (E : Finset (Sym2 V)) :
    edgeBoundary (sym2FinsetMap f E) = (edgeBoundary E).map f := by
  classical
  induction E using Finset.induction with
  | empty => simp [sym2FinsetMap, edgeBoundary]
  | @insert e E he ih =>
      have hmap : Sym2.map f e ∉ sym2FinsetMap f E := by
        intro h
        rw [sym2FinsetMap, Finset.mem_map] at h
        obtain ⟨e', he', heq⟩ := h
        exact he (Sym2.map.injective f.injective heq.symm ▸ he')
      have hleft :
          edgeBoundary (sym2FinsetMap f (insert e E)) =
            (Sym2.map f e).toFinset ∆
              edgeBoundary (sym2FinsetMap f E) := by
        have hmap' : (sym2MapEmbedding f) e ∉
            Finset.map (sym2MapEmbedding f) E := by
          intro hm
          apply hmap
          exact hm
        unfold sym2FinsetMap edgeBoundary
        rw [Finset.map_insert, Finset.fold_insert hmap']
        rfl
      have hright :
          edgeBoundary (insert e E) = e.toFinset ∆ edgeBoundary E := by
        unfold edgeBoundary
        rw [Finset.fold_insert he]
      rw [hleft, hright, ih, sym2_toFinset_map_embedding,
        finset_map_symmDiff]


end StatMech.FrontierB
