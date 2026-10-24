/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section32.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section30
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section30
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Closeds
import Mathlib.Algebra.FiveLemma
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set Function

namespace OrientationTheorem

variable {M : Type*} [TopologicalSpace M]

/-- **Conclusion of Theorem 32.1 for a compact subset `K`.** Packages the
two assertions of the orientation theorem for an `n`-manifold `M` and a
compact set `K ⊆ M`: the relative homology groups `Hrel q K` vanish for
`q > n`, and the comparison map `jMap K : Hrel n K → Γsec K` to sections
of the orientation sheaf is a bijection. Stated abstractly so that the
proof structure of Section 32 can be reused for any homology theory
`Hrel`/section functor `Γsec` satisfying the appropriate axioms. -/
structure OrientationTheoremResult
    (n : ℕ)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (Hrel : ℕ → Set M → Type*)
    [inst : ∀ q A, AddCommGroup (Hrel q A)]
    (Γsec : Set M → Type*)
    [inst' : ∀ A, AddCommGroup (Γsec A)]
    (jMap : (A : Set M) → Hrel n A →+ Γsec A)
    (K : Set M) : Prop where
  vanishing : ∀ q, q > n → ∀ x : Hrel q K, x = 0
  isomorphism : Bijective (jMap K)

/-- **Mayer–Vietoris ladder data for Proposition 32.2.** Records the
relevant portion of the commutative diagram with exact rows used to prove
that if the orientation theorem holds for `A`, `B`, and `A ∩ B`, then it
holds for `A ∪ B`: the top row is the relative-homology Mayer–Vietoris
sequence at degrees `n` and `q > n`, the bottom row is the
Mayer–Vietoris sequence for sections of the orientation sheaf, and
`jMap` provides the comparison map between them. -/
structure MayerVietorisLadder
    (n : ℕ)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)
    (A B : Set M) where
  mvα : Hrel n (A ∪ B) →+ Hrel n A × Hrel n B
  mvβ : Hrel n A × Hrel n B →+ Hrel n (A ∩ B)
  secα : Γsec (A ∪ B) →+ Γsec A × Γsec B
  secβ : Γsec A × Γsec B →+ Γsec (A ∩ B)
  mv_inj : ∀ x, mvα x = 0 → x = 0
  mv_exact : Exact mvα mvβ
  sec_inj : ∀ x, secα x = 0 → x = 0
  sec_exact : Exact secα secβ
  comm_α : secα.comp (jMap (A ∪ B)) =
    (AddMonoidHom.prodMap (jMap A) (jMap B)).comp mvα
  comm_β : secβ.comp (AddMonoidHom.prodMap (jMap A) (jMap B)) =
    (jMap (A ∩ B)).comp mvβ
  mv_inj_q : ∀ q, q > n →
    ∃ (αq : Hrel q (A ∪ B) →+ Hrel q A × Hrel q B),
      ∀ x, αq x = 0 → x = 0

/-- Build a `MayerVietorisLadder` from the full Mayer–Vietoris long exact
sequences in `Hrel` and `Γsec` together with the commutation hypotheses.
Uses the vanishing part of the orientation theorem on `A ∩ B` to derive
injectivity of `mvα` and of the higher-degree maps `mvα_q` for `q > n`,
since their kernels lie in `Hrel (q+1) (A ∩ B) = 0`. -/
def MayerVietorisLadder.ofExactSequences
    (n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)
    (A B : Set M) (_hA : IsClosed A) (_hB : IsClosed B)
    (_hOT_AB : OrientationTheoremResult n Hrel Γsec jMap (A ∩ B))

    (mvα_q : ∀ q, Hrel q (A ∪ B) →+ Hrel q A × Hrel q B)
    (mvβ_q : ∀ q, Hrel q A × Hrel q B →+ Hrel q (A ∩ B))
    (mvδ_q : ∀ q, Hrel (q + 1) (A ∩ B) →+ Hrel q (A ∪ B))

    (mv_exact_δα : ∀ q, Exact (mvδ_q q) (mvα_q q))
    (mv_exact_αβ : ∀ q, Exact (mvα_q q) (mvβ_q q))

    (secα : Γsec (A ∪ B) →+ Γsec A × Γsec B)
    (secβ : Γsec A × Γsec B →+ Γsec (A ∩ B))
    (sec_inj : ∀ x, secα x = 0 → x = 0)
    (sec_exact : Exact secα secβ)

    (comm_α : secα.comp (jMap (A ∪ B)) =
      (AddMonoidHom.prodMap (jMap A) (jMap B)).comp (mvα_q n))
    (comm_β : secβ.comp (AddMonoidHom.prodMap (jMap A) (jMap B)) =
      (jMap (A ∩ B)).comp (mvβ_q n)) :
    MayerVietorisLadder n Hrel Γsec jMap A B where
  mvα := mvα_q n
  mvβ := mvβ_q n
  secα := secα
  secβ := secβ
  mv_inj := by


    intro x hx

    obtain ⟨y, rfl⟩ := (mv_exact_δα n x).mp hx

    have hy : y = 0 := _hOT_AB.vanishing (n + 1) (by omega) y
    rw [hy, map_zero]
  mv_exact := mv_exact_αβ n
  sec_inj := sec_inj
  sec_exact := sec_exact
  comm_α := comm_α
  comm_β := comm_β
  mv_inj_q := by
    intro q hq
    exact ⟨mvα_q q, by
      intro x hx
      obtain ⟨y, rfl⟩ := (mv_exact_δα q x).mp hx

      have hy : y = 0 := _hOT_AB.vanishing (q + 1) (by omega) y
      rw [hy, map_zero]⟩

/-- Abstract data of the relative Mayer–Vietoris long exact sequences in
all degrees together with the section-sequence and compatibility
conditions, packaged so that `MayerVietorisLadder.ofExactSequences` can
be invoked from a single bundle. -/
structure RelativeMVSequenceData
    {M : Type*} [TopologicalSpace M]
    (n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)
    (A B : Set M) where
  mvα_q : ∀ q, Hrel q (A ∪ B) →+ Hrel q A × Hrel q B
  mvβ_q : ∀ q, Hrel q A × Hrel q B →+ Hrel q (A ∩ B)
  mvδ_q : ∀ q, Hrel (q + 1) (A ∩ B) →+ Hrel q (A ∪ B)
  mv_exact_δα : ∀ q, Exact (mvδ_q q) (mvα_q q)
  mv_exact_αβ : ∀ q, Exact (mvα_q q) (mvβ_q q)
  secα : Γsec (A ∪ B) →+ Γsec A × Γsec B
  secβ : Γsec A × Γsec B →+ Γsec (A ∩ B)
  sec_inj : ∀ x, secα x = 0 → x = 0
  sec_exact : Exact secα secβ
  comm_α : secα.comp (jMap (A ∪ B)) =
    (AddMonoidHom.prodMap (jMap A) (jMap B)).comp (mvα_q n)
  comm_β : secβ.comp (AddMonoidHom.prodMap (jMap A) (jMap B)) =
    (jMap (A ∩ B)).comp (mvβ_q n)

/-- Abstract data witnessing that `G (⋂ j, A j)` is the colimit of the
sequence `G (A i)` along the inclusions `A (i+1) ⊆ A i`: restriction
maps `ρ i` to the intersection, transition maps `φ i j` compatible with
them, and the two filtered-colimit conditions (every element of the
limit comes from some `G (A i)`, and an element vanishing in the limit
already vanishes at some larger stage). -/
structure RelativeHomologyColimitData {X : Type*} [TopologicalSpace X]
    (A : ℕ → Set X)
    (G : Set X → Type*)
    [∀ K, AddCommGroup (G K)] where
  ρ : ∀ i, G (A i) →+ G (⋂ j, A j)
  φ : ∀ (i j : ℕ), i ≤ j → G (A i) →+ G (A j)
  compat : ∀ i j (hij : i ≤ j), (ρ j).comp (φ i j hij) = ρ i
  surj : ∀ (x : G (⋂ j, A j)), ∃ i, ∃ g : G (A i), ρ i g = x
  inj : ∀ i (g : G (A i)), ρ i g = 0 → ∃ j, ∃ hij : i ≤ j, φ i j hij g = 0

/-- Bundle of all colimit data needed for the `orientation_theorem_iInter`
proof at a single decreasing compact sequence: per-degree
`RelativeHomologyColimitData` for `Hrel q`, one for `Γsec`, and the
compatibility of `jMap` with the restriction and transition maps. -/
structure ColimitDataForDecreasingCompact {M : Type*} [TopologicalSpace M]
    (n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : ℕ → Set M)
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K) where
  colH : ∀ q, RelativeHomologyColimitData A (Hrel q)
  colΓ : RelativeHomologyColimitData A Γsec
  hjMap_ρ : ∀ i, (colΓ.ρ i).comp (jMap (A i)) = (jMap (⋂ j, A j)).comp ((colH n).ρ i)
  hjMap_φ : ∀ i j (hij : i ≤ j),
    (colΓ.φ i j hij).comp (jMap (A i)) = (jMap (A j)).comp ((colH n).φ i j hij)

/-- Companion to `compact_decreasing_sequence_subset_open` rephrased in
complement form: if `K` is a compact subset of the complement of
`⋂ i, A i` where `A i` is a decreasing sequence of closed sets, then
`K ⊆ (A i)ᶜ` already for some `i`. Proved using the directed-cover
formulation of compactness. -/
lemma compact_subset_complement_eventually_aux
    {X : Type*} [TopologicalSpace X]
    (A : ℕ → Set X) (hA_closed : ∀ i, IsClosed (A i))
    (hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
    (K : Set X) (hK : IsCompact K)
    (hKA : K ⊆ (⋂ i, A i)ᶜ) :
    ∃ i, K ⊆ (A i)ᶜ := by
  rw [compl_iInter] at hKA
  exact hK.elim_directed_cover _ (fun i => (hA_closed i).isOpen_compl) hKA
    (Monotone.directed_le (fun i j hij =>
      compl_subset_compl.mpr (antitone_nat_of_succ_le hA_decreasing hij)))

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
