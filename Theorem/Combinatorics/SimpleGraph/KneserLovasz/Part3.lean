/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Instance.Combinatorics.SimpleGraph.KneserLovasz.Part2
/-!
# Kneser–Lovász theorem

For `0 < k` and `2 * k ≤ n`, the Kneser graph on the `k`-subsets of an
`n`-element set has chromatic number `n - 2 * k + 2`.
-/


namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

open Finset

theorem knNegCell_consistent {n : ℕ} {x : Finset (Bool × Fin n)}
    (hcons : knConsistent x) : knConsistent (knNegCell x) := by
  classical
  intro l hl hnl
  obtain ⟨m, hm, hml⟩ := knMem_negCell.mp hl
  obtain ⟨m', hm', hm'l⟩ := knMem_negCell.mp hnl
  have hme : m' = l := knNegLabel_inj hm'l
  have hmem : knNegLabel m ∈ x := by
    rw [hml]
    rw [hme] at hm'
    exact hm'
  exact hcons m hm hmem

theorem knNegChain {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (h : knChain σ) : knChain (σ.image knNegCell) := by
  classical
  obtain ⟨hne, hcons, hisch⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨knNegCell x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    rw [← hxy]
    exact knNegCell_consistent (hcons x hx)
  · intro a ha b hb
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp ha
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hb
    rcases hisch x hx z hz with hsub | hsub
    · left
      rw [← hxy, ← hzy]
      exact knNegCell_mono hsub
    · right
      rw [← hxy, ← hzy]
      exact knNegCell_mono hsub

theorem knNegTight {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (hanti : knAntipodal L)
    (h : knTight σ L) (hne : ∀ x ∈ σ, x.Nonempty) :
    knTight (σ.image knNegCell) L := by
  classical
  obtain ⟨⟨hchain, hsub⟩, hcard⟩ := h
  have hchainI := knNegChain σ hchain
  have htopI : knTop (σ.image knNegCell) = knNegCell (knTop σ) :=
    knNegTop σ hchain
  have himgI : knImg (σ.image knNegCell) L = knNegCell (knImg σ L) := by
    ext ℓ
    constructor
    · intro hm
      obtain ⟨y, hy, hyl⟩ := Finset.mem_image.mp hm
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      have hxL : L (knNegCell x) = knNegLabel (L x) :=
        hanti x (hchain.2.1 x hx) (hne x hx)
      rw [← hxy] at hyl
      rw [hxL] at hyl
      have hmem : knNegLabel (L x) ∈ knNegCell (knImg σ L) :=
        knNegLabel_mem_negCell (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      rwa [hyl] at hmem
    · intro hm
      obtain ⟨m, hm2, hml⟩ := knMem_negCell.mp hm
      obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hm2
      have hxL : L (knNegCell x) = knNegLabel (L x) :=
        hanti x (hchain.2.1 x hx) (hne x hx)
      have hmemI : knNegCell x ∈ σ.image knNegCell :=
        Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have hmemL : L (knNegCell x) ∈ knImg (σ.image knNegCell) L :=
        Finset.mem_image.mpr ⟨knNegCell x, hmemI, rfl⟩
      rw [hxL, hxm, hml] at hmemL
      exact hmemL
  refine ⟨⟨hchainI, ?_⟩, ?_⟩
  · rw [htopI, himgI]
    exact knNegCell_mono hsub
  · rw [htopI, knNegCell_card,
      Finset.card_image_of_injective σ knNegCell_injective]
    exact hcard

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted
