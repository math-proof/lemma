/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.TIChoquetClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Theorem.StatisticalMechanics.Code.Foundations.CondDistribution.Part4
import Def.StatisticalMechanics.Code.Ising.AeTailInvariantClose.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech symmDiff

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


theorem aetc_outsideSigma_box_antitone {j n : ℕ} (h : j ≤ n) :
    outsideSigma (box d n) ≤ outsideSigma (box d j) :=
  iSup₂_mono' fun e he => ⟨e, fun hc => he (box_mono d h hc), le_rfl⟩


theorem aetc_isTailEvent_liminf (A : ℕ → Set (ConfigSpace (Site d)))
    (hA : ∀ n, @MeasurableSet _ (outsideSigma (box d n)) (A n)) :
    IsTailEvent (d := d) (⋃ N, ⋂ i, A (i + N)) := by
  intro j
  have hmono : Monotone (fun N => ⋂ i, A (i + N)) := by
    intro N M hNM
    refine Set.iInter_mono' fun i => ⟨i + (M - N), ?_⟩
    have hi : i + (M - N) + N = i + M := by omega
    rw [hi]
  have hrw : (⋃ N, ⋂ i, A (i + N)) = ⋃ N, ⋂ i, A (i + (N + j)) := by
    apply le_antisymm
    · exact Set.iUnion_mono' fun N => ⟨N, hmono (by omega)⟩
    · exact Set.iUnion_mono' fun N => ⟨N + j, le_rfl⟩
  rw [hrw]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun i => ?_
  exact aetc_outsideSigma_box_antitone (by omega) _ (hA (i + (N + j)))


theorem aetc_aeTail_of_approxFarOut {μ : Measure (ConfigSpace (Site d))} [IsFiniteMeasure μ]
    {s : Set (ConfigSpace (Site d))} (happ : AeApproxFarOut μ s) :
    ∃ s' : Set (ConfigSpace (Site d)), IsTailEvent (d := d) s' ∧ s =ᵐ[μ] s' := by
  
  have hpos : ∀ n : ℕ, (0 : ENNReal) < ((2 : ENNReal)⁻¹) ^ n := fun n =>
    ENNReal.pow_pos (by simp) n
  have hchoice : ∀ n : ℕ, ∃ A : Set (ConfigSpace (Site d)),
      @MeasurableSet _ (outsideSigma (box d n)) A ∧ μ (s ∆ A) < ((2 : ENNReal)⁻¹) ^ n :=
    fun n => happ n (((2 : ENNReal)⁻¹) ^ n) (hpos n)
  choose A hAmeas hAlt using hchoice
  
  refine ⟨⋃ N, ⋂ i, A (i + N), aetc_isTailEvent_liminf A hAmeas, ?_⟩
  
  have hsumm : ∑' n, μ (s ∆ A n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => (hAlt n).le)
    rw [ENNReal.tsum_geometric]; simp
  have hfin : ∀ᵐ x ∂μ, {n | x ∈ s ∆ A n}.Finite := ae_finite_setOf_mem hsumm
  
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
    have := hN hmem; omega
  have hmemset : (x ∈ ⋃ N, ⋂ i, A (i + N)) ↔ ∀ᶠ n in atTop, x ∈ A n := by
    simp only [mem_iUnion, mem_iInter]
    rw [Filter.eventually_atTop]
    constructor
    · rintro ⟨N, hN⟩
      exact ⟨N, fun n hn => by have := hN (n - N); rwa [Nat.sub_add_cancel hn] at this⟩
    · rintro ⟨N, hN⟩; exact ⟨N, fun i => hN (i + N) (Nat.le_add_left N i)⟩
  rw [hmemset]
  constructor
  · intro hxs; exact hev.mono fun n hn => hn.mp hxs
  · intro hxA; obtain ⟨n, hn1, hn2⟩ := (hev.and hxA).exists; exact hn1.mpr hn2


theorem aetc_haeTail (hd : 1 ≤ d) {μ : Measure (ConfigSpace (Site d))} [IsFiniteMeasure μ]
    (hμ : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    ∀ s : Set (ConfigSpace (Site d)), MeasurableSet s →
      (∀ g : Multiplicative (Site d),
        (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) →
        ∃ s' : Set (ConfigSpace (Site d)), IsTailEvent (d := d) s' ∧ s =ᵐ[μ] s' := by
  intro s hs hinv
  exact aetc_aeTail_of_approxFarOut (fun k ε hε => aetc_invariant_approx hd hμ hs hinv k hε)


theorem aetc_plusState_isErgodic (β h : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d)))) :
    IsErgodic (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  tic_plusState_isErgodic_of_aeTailInvariant β h hβ hh hti hdlr (aetc_haeTail hd hti)


theorem aetc_minusState_isErgodic (β h : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d)))) :
    IsErgodic (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))) :=
  tic_minusState_isErgodic_of_aeTailInvariant β h hβ hh hti hdlr (aetc_haeTail hd hti)


theorem aetc_dirac_const_isTranslationInvariant :
    IsTranslationInvariant (G := Multiplicative (Site d))
      (Measure.dirac (fun _ => true) : Measure (ConfigSpace (Site d))) := by
  intro g
  refine ⟨measurable_shift g, ?_⟩
  rw [Measure.map_dirac' (measurable_shift g)]
  have hfix : (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) (fun _ => true)
      = (fun _ => true) := by funext e; simp [shift]
  rw [hfix]


theorem aetc_haeTail_nonvacuous :
    ∃ s' : Set (ConfigSpace (Site 1)), IsTailEvent (d := 1) s'
      ∧ (Set.univ : Set (ConfigSpace (Site 1)))
          =ᵐ[(Measure.dirac (fun _ => true) : Measure (ConfigSpace (Site 1)))] s' :=
  aetc_haeTail (d := 1) le_rfl aetc_dirac_const_isTranslationInvariant Set.univ
    MeasurableSet.univ (fun _ => Set.preimage_univ)

end Ising
end StatMech
