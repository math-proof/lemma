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
import Def.StatisticalMechanics.Code.Ising.AeTailInvariantClose
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech symmDiff

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


theorem aetc_finSig_mono {F G : Finset (Site d)} (h : F ⊆ G) :
    aetc_finSig F ≤ aetc_finSig G :=
  iSup₂_mono' fun e he => ⟨e, h he, le_rfl⟩


theorem aetc_isSetRing_Cring : IsSetRing (aetc_Cring d) := by
  refine ⟨⟨∅, @MeasurableSet.empty _ (aetc_finSig ∅)⟩, ?_, ?_⟩
  · rintro A B ⟨F, hA⟩ ⟨G, hB⟩
    exact ⟨F ∪ G, (aetc_finSig_mono Finset.subset_union_left _ hA).union
      (aetc_finSig_mono Finset.subset_union_right _ hB)⟩
  · rintro A B ⟨F, hA⟩ ⟨G, hB⟩
    exact ⟨F ∪ G, (aetc_finSig_mono Finset.subset_union_left _ hA).diff
      (aetc_finSig_mono Finset.subset_union_right _ hB)⟩


theorem aetc_univ_mem_Cring : (Set.univ : Set (ConfigSpace (Site d))) ∈ aetc_Cring d :=
  ⟨∅, @MeasurableSet.univ _ (aetc_finSig ∅)⟩


theorem aetc_generateFrom_Cring :
    (inferInstance : MeasurableSpace (ConfigSpace (Site d))) = generateFrom (aetc_Cring d) := by
  apply le_antisymm
  · rw [measurableSpace_eq_iSup_comap]
    refine iSup_le fun e => fun A hA => measurableSet_generateFrom ⟨{e}, ?_⟩
    have : aetc_finSig ({e} : Finset (Site d))
        = MeasurableSpace.comap (ConfigSpace.eval e) inferInstance := by simp [aetc_finSig]
    rw [this]; exact hA
  · refine generateFrom_le ?_
    rintro A ⟨F, hF⟩
    exact (iSup₂_le fun e _ => (ConfigSpace.measurable_eval e).comap_le) A hF


theorem aetc_shift_measurable (g : Multiplicative (Site d)) (F : Finset (Site d)) :
    @Measurable (ConfigSpace (Site d)) (ConfigSpace (Site d))
      (aetc_finSig (F.image (fun e => g⁻¹ • e))) (aetc_finSig F) (shift g) := by
  refine Measurable.of_comap_le ?_
  rw [show aetc_finSig F
      = ⨆ e ∈ F, MeasurableSpace.comap (ConfigSpace.eval e) inferInstance from rfl,
      MeasurableSpace.comap_iSup]
  refine iSup_le fun e => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun he => ?_
  rw [comap_comp]
  have heq : (ConfigSpace.eval e ∘ shift g) = ConfigSpace.eval (g⁻¹ • e) := by
    funext ω; simp [ConfigSpace.eval, shift]
  rw [heq]
  exact le_iSup₂_of_le (g⁻¹ • e) (Finset.mem_image_of_mem _ he) le_rfl


theorem aetc_finSig_le_outsideSigma (F : Finset (Site d)) (Λ : Set (Site d))
    (h : (↑F : Set (Site d)) ⊆ Λᶜ) : aetc_finSig F ≤ outsideSigma Λ :=
  iSup₂_mono' fun e he => ⟨e, h he, le_rfl⟩


theorem aetc_exists_shift_outside (hd : 1 ≤ d) (F : Finset (Site d)) (k : ℕ) :
    ∃ g : Multiplicative (Site d), (↑(F.image (fun e => g⁻¹ • e)) : Set (Site d)) ⊆ (box d k)ᶜ := by
  
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ e ∈ F, (e ⟨0, hd⟩).natAbs ≤ M :=
    ⟨(F.sup fun e => (e ⟨0, hd⟩).natAbs),
      fun e he => Finset.le_sup (f := fun e => (e ⟨0, hd⟩).natAbs) he⟩
  set g : Multiplicative (Site d) :=
    Multiplicative.ofAdd (fun i => if i = ⟨0, hd⟩ then (M + k + 1 : ℤ) else 0) with hg
  refine ⟨g, ?_⟩
  intro y hy
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy
  obtain ⟨e, he, rfl⟩ := hy
  rw [Set.mem_compl_iff, box, Set.mem_setOf_eq, not_forall]
  refine ⟨⟨0, hd⟩, ?_⟩
  
  have hval : (g⁻¹ • e) ⟨0, hd⟩ = e ⟨0, hd⟩ - (M + k + 1 : ℤ) := by
    show (-(Multiplicative.toAdd g) + e) ⟨0, hd⟩ = _
    rw [hg]
    show -(if (⟨0, hd⟩ : Fin d) = ⟨0, hd⟩ then (M + k + 1 : ℤ) else 0) + e ⟨0, hd⟩ = _
    rw [if_pos rfl]; ring
  rw [not_le, hval]
  
  have h2 : e ⟨0, hd⟩ ≤ (M : ℤ) := by have := Int.le_natAbs (a := e ⟨0, hd⟩); have := hM e he; omega
  have h3 : e ⟨0, hd⟩ - (M + k + 1 : ℤ) ≤ -(k + 1 : ℤ) := by omega
  zify; rw [Int.abs_eq_natAbs] at *; omega


theorem aetc_symmDiff_preimage_invariant {μ : Measure (ConfigSpace (Site d))}
    (hμ : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    {s A : Set (ConfigSpace (Site d))} (hs : MeasurableSet s) (hA : MeasurableSet A)
    (g : Multiplicative (Site d)) (hinv : shift g ⁻¹' s = s) :
    μ (s ∆ (shift g ⁻¹' A)) = μ (s ∆ A) := by
  have hpre : shift g ⁻¹' (s ∆ A) = s ∆ (shift g ⁻¹' A) := by
    rw [Set.preimage_symmDiff, hinv]
  calc μ (s ∆ (shift g ⁻¹' A)) = μ (shift g ⁻¹' (s ∆ A)) := by rw [hpre]
    _ = μ (s ∆ A) := (hμ g).measure_preimage (hs.symmDiff hA).nullMeasurableSet


theorem aetc_invariant_approx (hd : 1 ≤ d) {μ : Measure (ConfigSpace (Site d))} [IsFiniteMeasure μ]
    (hμ : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    {s : Set (ConfigSpace (Site d))} (hs : MeasurableSet s)
    (hinv : ∀ g : Multiplicative (Site d),
      (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s)
    (k : ℕ) {ε : ENNReal} (hε : 0 < ε) :
    ∃ A : Set (ConfigSpace (Site d)), @MeasurableSet _ (outsideSigma (box d k)) A
      ∧ μ (s ∆ A) < ε := by
  
  have hcover : ∃ D : Set (Set (ConfigSpace (Site d))), D.Countable ∧ D ⊆ aetc_Cring d
      ∧ μ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact aetc_univ_mem_Cring
    · simp
  obtain ⟨A₀, hA₀mem, hA₀⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing aetc_isSetRing_Cring hcover
      aetc_generateFrom_Cring hs hε
  obtain ⟨F₀, hF₀⟩ := hA₀mem
  have hA₀meas : MeasurableSet A₀ :=
    (aetc_finSig_le_outsideSigma F₀ (∅ : Set (Site d)) (by simp)).trans
      (outsideSigma_le _) A₀ hF₀
  
  obtain ⟨g, hgout⟩ := aetc_exists_shift_outside hd F₀ k
  refine ⟨shift g ⁻¹' A₀, ?_, ?_⟩
  · 
    have hsm : @MeasurableSet _ (aetc_finSig (F₀.image (fun e => g⁻¹ • e))) (shift g ⁻¹' A₀) :=
      aetc_shift_measurable g F₀ hF₀
    exact aetc_finSig_le_outsideSigma _ _ hgout _ hsm
  · 
    have hdist : μ (s ∆ (shift g ⁻¹' A₀)) = μ (s ∆ A₀) :=
      aetc_symmDiff_preimage_invariant hμ hs hA₀meas g (hinv g)
    rw [hdist, symmDiff_comm s A₀]
    exact hA₀


end Ising
end StatMech
