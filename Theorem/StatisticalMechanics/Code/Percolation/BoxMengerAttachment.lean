/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bma_internal_of_edgesIn {R : Set (Site d)} {W : Finset (Sym2 (Site d))}
    (hW : ∀ e ∈ W, ∀ p, p ∈ e → p ∈ R) :
    ∀ u v, u ∈ R → s(u, v) ∈ W → v ∈ R := by
  intro u v _ hmem
  exact hW _ hmem v (Sym2.mem_mk_right u v)


theorem bma_internal_of_edgesIn_disjoint {R S : Set (Site d)} {W : Finset (Sym2 (Site d))}
    (hW : ∀ e ∈ W, ∀ p, p ∈ e → p ∈ S) (hdisj : Disjoint R S) :
    ∀ u v, u ∈ R → s(u, v) ∈ W → v ∈ R := by
  intro u v hu hmem
  have huS : u ∈ S := hW _ hmem u (Sym2.mem_mk_left u v)
  exact absurd (Set.disjoint_left.mp hdisj hu huS).elim (fun h => h)


theorem bma_internal_union {R₁ R₂ R₃ : Set (Site d)} {W₁ W₂ W₃ : Finset (Sym2 (Site d))}
    (h1 : ∀ e ∈ W₁, ∀ p, p ∈ e → p ∈ R₁) (h2 : ∀ e ∈ W₂, ∀ p, p ∈ e → p ∈ R₂)
    (h3 : ∀ e ∈ W₃, ∀ p, p ∈ e → p ∈ R₃)
    (hd12 : Disjoint R₁ R₂) (hd13 : Disjoint R₁ R₃) :
    ∀ u v, u ∈ R₁ → s(u, v) ∈ W₁ ∪ W₂ ∪ W₃ → v ∈ R₁ := by
  classical
  intro u v hu hmem
  rw [Finset.mem_union, Finset.mem_union] at hmem
  rcases hmem with (h | h) | h
  · exact bma_internal_of_edgesIn h1 u v hu h
  · exact bma_internal_of_edgesIn_disjoint h2 hd12 u v hu h
  · exact bma_internal_of_edgesIn_disjoint h3 hd13 u v hu h


theorem bma_originAvoiding_union {W₁ W₂ W₃ : Finset (Sym2 (Site d))}
    (h1 : ∀ e ∈ W₁, (0 : Site d) ∉ e) (h2 : ∀ e ∈ W₂, (0 : Site d) ∉ e)
    (h3 : ∀ e ∈ W₃, (0 : Site d) ∉ e) :
    ∀ e ∈ W₁ ∪ W₂ ∪ W₃, (0 : Site d) ∉ e := by
  classical
  intro e he
  rw [Finset.mem_union, Finset.mem_union] at he
  rcases he with (h | h) | h
  · exact h1 e h
  · exact h2 e h
  · exact h3 e h


theorem bma_removeSite_forceOpen_mono_sub (ω : ConfigSpace (Sym2 (Site d)))
    {Wⱼ W : Finset (Sym2 (Site d))} (hsub : Wⱼ ⊆ W) :
    removeSite 0 (forceOpenFinset Wⱼ ω) ≤ removeSite 0 (forceOpenFinset W ω) := by
  classical
  intro e
  by_cases h0 : (0 : Site d) ∈ e
  · simp [removeSite, h0]
  · simp only [removeSite, h0, if_false]
    unfold forceOpenFinset
    by_cases hj : e ∈ Wⱼ
    · simp [hj, hsub hj]
    · by_cases hW : e ∈ W <;> simp [hj, hW]


theorem bma_connected_of_sub (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    {Wⱼ W : Finset (Sym2 (Site d))} (hsub : Wⱼ ⊆ W)
    (hc : Connected d (removeSite 0 (forceOpenFinset Wⱼ ω)) a x) :
    Connected d (removeSite 0 (forceOpenFinset W ω)) a x :=
  connected_mono (bma_removeSite_forceOpen_mono_sub ω hsub) hc


end Percolation
end StatMech
