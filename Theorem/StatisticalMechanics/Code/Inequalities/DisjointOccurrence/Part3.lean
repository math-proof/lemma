/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3


namespace StatMech

open ConfigSpace

variable {E : Type*}


lemma mem_disjointOccurrence {A B : Set (ConfigSpace E)} {ω : ConfigSpace E} :
    ω ∈ disjointOccurrence A B ↔
      ∃ K L : Set E, Disjoint K L ∧ OccursOn A K ω ∧ OccursOn B L ω :=
  Iff.rfl


lemma disjointOccurrence_notation (A B : Set (ConfigSpace E)) :
    (A □ B : Set (ConfigSpace E)) = disjointOccurrence A B := rfl


theorem disjointOccurrence_subset_inter (A B : Set (ConfigSpace E)) :
    disjointOccurrence A B ⊆ A ∩ B := by
  rintro ω ⟨K, L, _, hA, hB⟩
  exact ⟨hA.mem_self, hB.mem_self⟩


theorem disjointOccurrence_comm (A B : Set (ConfigSpace E)) :
    disjointOccurrence A B = disjointOccurrence B A := by
  ext ω
  constructor
  · rintro ⟨K, L, hKL, hA, hB⟩
    exact ⟨L, K, hKL.symm, hB, hA⟩
  · rintro ⟨K, L, hKL, hB, hA⟩
    exact ⟨L, K, hKL.symm, hA, hB⟩


theorem disjointOccurrence_mono {A A' B B' : Set (ConfigSpace E)}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    disjointOccurrence A B ⊆ disjointOccurrence A' B' := by
  rintro ω ⟨K, L, hKL, hAK, hBL⟩
  exact ⟨K, L, hKL, hAK.mono_event hA, hBL.mono_event hB⟩

end StatMech
