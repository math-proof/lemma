/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.CondDistribution.Part4
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.Foundations.AeTailInvariant.Part4
open MeasureTheory MeasurableSpace Set Filter
open scoped ENNReal symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false


namespace StatMech

open ConfigSpace

variable {E H : Type*} [Countable E] [DecidableEq E]
  [Group H] [MulAction H E]


theorem atiOutsideSigma_antitone {window : ℕ → Set E}
    (hwindow : Monotone window) {j n : ℕ} (h : j ≤ n) :
    outsideSigma (window n) ≤ outsideSigma (window j) :=
  iSup₂_mono' fun e he => ⟨e, fun hc => he (hwindow h hc), le_rfl⟩

theorem atiTailEvent_liminf {window : ℕ → Set E}
    (hwindow : Monotone window)
    (A : ℕ → Set (ConfigSpace E))
    (hA : ∀ n, @MeasurableSet _ (outsideSigma (window n)) (A n)) :
    AtiTailEvent window (⋃ N, ⋂ i, A (i + N)) := by
  intro j
  have hmono : Monotone (fun N => ⋂ i, A (i + N)) := by
    intro N M hNM
    refine Set.iInter_mono' fun i => ⟨i + (M - N), ?_⟩
    have hi : i + (M - N) + N = i + M := by omega
    rw [hi]
  have hrw : (⋃ N, ⋂ i, A (i + N)) =
      ⋃ N, ⋂ i, A (i + (N + j)) := by
    apply le_antisymm
    · exact Set.iUnion_mono' fun N => ⟨N, hmono (by omega)⟩
    · exact Set.iUnion_mono' fun N => ⟨N + j, le_rfl⟩
  rw [hrw]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun i => ?_
  exact atiOutsideSigma_antitone hwindow (by omega) _ (hA (i + (N + j)))

theorem ati_aeTail_of_approxFarOut {window : ℕ → Set E}
    (hwindow : Monotone window)
    {mu : Measure (ConfigSpace E)} [IsFiniteMeasure mu]
    {s : Set (ConfigSpace E)} (happ : AtiApproxFarOut window mu s) :
    ∃ s' : Set (ConfigSpace E), AtiTailEvent window s' ∧ s =ᵐ[mu] s' := by
  have hpos : ∀ n : ℕ, (0 : ENNReal) < ((2 : ENNReal)⁻¹) ^ n :=
    fun n => ENNReal.pow_pos (by simp) n
  have hchoice : ∀ n : ℕ, ∃ A : Set (ConfigSpace E),
      @MeasurableSet _ (outsideSigma (window n)) A ∧
        mu (s ∆ A) < ((2 : ENNReal)⁻¹) ^ n :=
    fun n => happ n (((2 : ENNReal)⁻¹) ^ n) (hpos n)
  choose A hAmeas hAlt using hchoice
  refine ⟨⋃ N, ⋂ i, A (i + N), atiTailEvent_liminf hwindow A hAmeas, ?_⟩
  have hsumm : ∑' n, mu (s ∆ A n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_
      (ENNReal.tsum_le_tsum fun n => (hAlt n).le)
    rw [ENNReal.tsum_geometric]
    simp
  have hfin : ∀ᵐ x ∂mu, {n | x ∈ s ∆ A n}.Finite :=
    ae_finite_setOf_mem hsumm
  rw [Filter.eventuallyEq_set]
  filter_upwards [hfin] with x hx
  have hev : ∀ᶠ n in atTop, (x ∈ s ↔ x ∈ A n) := by
    rw [eventually_atTop]
    obtain ⟨N, hN⟩ := hx.bddAbove
    refine ⟨N + 1, fun n hn => ?_⟩
    by_contra hne
    have hmem : n ∈ {n | x ∈ s ∆ A n} := by
      simp only [mem_setOf_eq, Set.mem_symmDiff]
      by_cases hxs : x ∈ s
      · exact Or.inl ⟨hxs, fun hA => hne (iff_of_true hxs hA)⟩
      · exact Or.inr ⟨by by_contra hA; exact hne (iff_of_false hxs hA), hxs⟩
    have := hN hmem
    omega
  have hmemset : (x ∈ ⋃ N, ⋂ i, A (i + N)) ↔
      ∀ᶠ n in atTop, x ∈ A n := by
    simp only [mem_iUnion, mem_iInter]
    rw [Filter.eventually_atTop]
    constructor
    · rintro ⟨N, hN⟩
      exact ⟨N, fun n hn => by
        have := hN (n - N)
        rwa [Nat.sub_add_cancel hn] at this⟩
    · rintro ⟨N, hN⟩
      exact ⟨N, fun i => hN (i + N) (Nat.le_add_left N i)⟩
  rw [hmemset]
  constructor
  · intro hxs
    exact hev.mono fun n hn => hn.mp hxs
  · intro hxA
    obtain ⟨n, hn1, hn2⟩ := (hev.and hxA).exists
    exact hn1.mpr hn2


theorem ati_invariant_aeTail
    (window : ℕ → Set E) (hwindow : Monotone window)
    (hescape : ∀ (F : Finset E) (k : ℕ), ∃ g : H,
      (↑(F.image (fun e => g⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
    {mu : Measure (ConfigSpace E)} [IsFiniteMeasure mu]
    (hmu : IsTranslationInvariant (G := H) mu) :
    ∀ s : Set (ConfigSpace E), MeasurableSet s →
      (∀ g : H, shift g ⁻¹' s = s) →
      ∃ s' : Set (ConfigSpace E), AtiTailEvent window s' ∧ s =ᵐ[mu] s' := by
  intro s hs hinv
  exact ati_aeTail_of_approxFarOut hwindow
    (fun k ε hε => ati_invariant_approx window hescape hmu hs hinv k hε)


theorem ati_sequenceInvariant_aeTail
    (window : ℕ → Set E) (hwindow : Monotone window)
    (g : ℕ → H)
    (hescape : ∀ (F : Finset E) (k : ℕ), ∃ n : ℕ,
      (↑(F.image (fun e => (g n)⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
    {mu : Measure (ConfigSpace E)} [IsFiniteMeasure mu]
    (hmu : IsTranslationInvariant (G := H) mu) :
    ∀ s : Set (ConfigSpace E), MeasurableSet s →
      (∀ n : ℕ, shift (g n) ⁻¹' s = s) →
      ∃ s' : Set (ConfigSpace E), AtiTailEvent window s' ∧ s =ᵐ[mu] s' := by
  intro s hs hinv
  exact ati_aeTail_of_approxFarOut hwindow
    (fun k ε hε =>
      ati_sequenceInvariant_approx window g hescape hmu hs hinv k hε)

end StatMech
