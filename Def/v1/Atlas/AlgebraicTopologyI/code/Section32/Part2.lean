/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section32.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section30.Part4
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section30
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Closeds
import Mathlib.Algebra.FiveLemma
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section32
open Set Function


namespace OrientationTheorem

variable {M : Type*} [TopologicalSpace M]

/-- Manifold-flavoured constructor for
`ColimitDataForDecreasingCompact`: assembles the colimit data from the
manifold versions of the surjectivity and injectivity assertions, where
witnesses are presented as compact subsets of the complement of
`⋂ i, A i` and are converted to indices using
`compact_subset_complement_eventually_aux`. -/
def ColimitDataForDecreasingCompact.ofManifold
    {M : Type*} [TopologicalSpace M]
    (n : ℕ) [AlgebraicTopologyI.TopologicalManifold n M]
    (A : ℕ → Set M)
    (hA_compact : ∀ i, IsCompact (A i))
    (hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)

    (ρH : ∀ q, ∀ i, Hrel q (A i) →+ Hrel q (⋂ j, A j))
    (φH : ∀ q, ∀ (i j : ℕ), i ≤ j → Hrel q (A i) →+ Hrel q (A j))
    (hcompatH : ∀ q i j (hij : i ≤ j), (ρH q j).comp (φH q i j hij) = ρH q i)

    (hsurjH : ∀ q (x : Hrel q (⋂ j, A j)),
      ∃ (K : Set M), IsCompact K ∧ K ⊆ (⋂ i, A i)ᶜ ∧
        ∀ i, K ⊆ (A i)ᶜ → ∃ g : Hrel q (A i), ρH q i g = x)

    (hinjH : ∀ q (i : ℕ) (g : Hrel q (A i)), ρH q i g = 0 →
      ∃ (K : Set M), IsCompact K ∧ K ⊆ (⋂ k, A k)ᶜ ∧
        ∀ j (hij : i ≤ j), K ⊆ (A j)ᶜ → φH q i j hij g = 0)

    (ρΓ : ∀ i, Γsec (A i) →+ Γsec (⋂ j, A j))
    (φΓ : ∀ (i j : ℕ), i ≤ j → Γsec (A i) →+ Γsec (A j))
    (hcompatΓ : ∀ i j (hij : i ≤ j), (ρΓ j).comp (φΓ i j hij) = ρΓ i)

    (hsurjΓ : ∀ (x : Γsec (⋂ j, A j)),
      ∃ (K : Set M), IsCompact K ∧ K ⊆ (⋂ i, A i)ᶜ ∧
        ∀ i, K ⊆ (A i)ᶜ → ∃ g : Γsec (A i), ρΓ i g = x)

    (hinjΓ : ∀ (i : ℕ) (g : Γsec (A i)), ρΓ i g = 0 →
      ∃ (K : Set M), IsCompact K ∧ K ⊆ (⋂ k, A k)ᶜ ∧
        ∀ j (hij : i ≤ j), K ⊆ (A j)ᶜ → φΓ i j hij g = 0)

    (hjMap_ρ : ∀ i, (ρΓ i).comp (jMap (A i)) = (jMap (⋂ j, A j)).comp (ρH n i))

    (hjMap_φ : ∀ i j (hij : i ≤ j),
      (φΓ i j hij).comp (jMap (A i)) = (jMap (A j)).comp (φH n i j hij)) :
    ColimitDataForDecreasingCompact n A Hrel Γsec jMap where
  colH q := {
    ρ := ρH q
    φ := φH q
    compat := hcompatH q
    surj := by
      intro x
      obtain ⟨K, hK_compact, hK_sub, hK_lift⟩ := hsurjH q x
      have hA_closed : ∀ i, IsClosed (A i) := fun i =>
        (hA_compact i).isClosed
      obtain ⟨i, hKi⟩ := compact_subset_complement_eventually_aux A hA_closed
        hA_decreasing K hK_compact hK_sub
      obtain ⟨g, hg⟩ := hK_lift i hKi
      exact ⟨i, g, hg⟩
    inj := by
      intro i g hg
      obtain ⟨K, hK_compact, hK_sub, hK_vanish⟩ := hinjH q i g hg
      have hA_closed : ∀ i, IsClosed (A i) := fun i =>
        (hA_compact i).isClosed
      obtain ⟨j, hKj⟩ := compact_subset_complement_eventually_aux A hA_closed
        hA_decreasing K hK_compact hK_sub
      have hij : i ≤ max i j := le_max_left i j
      have hjmax : j ≤ max i j := le_max_right i j
      have hKmax : K ⊆ (A (max i j))ᶜ := hKj.trans
        (compl_subset_compl.mpr (antitone_nat_of_succ_le hA_decreasing hjmax))
      exact ⟨max i j, hij, hK_vanish (max i j) hij hKmax⟩
  }
  colΓ := {
    ρ := ρΓ
    φ := φΓ
    compat := hcompatΓ
    surj := by
      intro x
      obtain ⟨K, hK_compact, hK_sub, hK_lift⟩ := hsurjΓ x
      have hA_closed : ∀ i, IsClosed (A i) := fun i =>
        (hA_compact i).isClosed
      obtain ⟨i, hKi⟩ := compact_subset_complement_eventually_aux A hA_closed
        hA_decreasing K hK_compact hK_sub
      obtain ⟨g, hg⟩ := hK_lift i hKi
      exact ⟨i, g, hg⟩
    inj := by
      intro i g hg
      obtain ⟨K, hK_compact, hK_sub, hK_vanish⟩ := hinjΓ i g hg
      have hA_closed : ∀ i, IsClosed (A i) := fun i =>
        (hA_compact i).isClosed
      obtain ⟨j, hKj⟩ := compact_subset_complement_eventually_aux A hA_closed
        hA_decreasing K hK_compact hK_sub
      have hij : i ≤ max i j := le_max_left i j
      have hjmax : j ≤ max i j := le_max_right i j
      have hKmax : K ⊆ (A (max i j))ᶜ := hKj.trans
        (compl_subset_compl.mpr (antitone_nat_of_succ_le hA_decreasing hjmax))
      exact ⟨max i j, hij, hK_vanish (max i j) hij hKmax⟩
  }
  hjMap_ρ := hjMap_ρ
  hjMap_φ := hjMap_φ

end OrientationTheorem
