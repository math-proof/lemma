/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Def.StatisticalMechanics.Code.FK.FreeWeakLimit.Part7
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK

variable {d : ℕ}


theorem psiShiftFree_pos {d n : ℕ} {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : 0 < psiShiftFree d n ψ p q :=
  mul_pos (psiEdgeFactor_pos hp hp1) (pow_pos hq _)


theorem fkWeight_psiExt_free (d n : ℕ) {p q : ℝ} (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    fkWeight (boxGraph d (n+1)) p q (psiExt d n ψ ω)
      = bcWeight (boxGraph d n) (inducedWiringFree d n ψ) p q ω * psiShiftFree d n ψ p q := by
  rw [fkWeight, numClusters_psiExt_free, edgeProduct_psiExt, bcWeight, psiShiftFree, pow_add]
  ring


theorem inducedFkZ_innerEdgeFinset_psi_free (d n : ℕ) {p q : ℝ}
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    inducedFkZ (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ
      = bcZ (boxGraph d n) (inducedWiringFree d n ψ) p q * psiShiftFree d n ψ p q := by
  rw [inducedFkZ, condFibre_eq_image_psiExt,
    Finset.sum_image (fun a _ b _ h => by
      have := congrArg (innerRestrict d n) h
      rwa [innerRestrict_psiExt, innerRestrict_psiExt] at this),
    bcZ, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ω _ => fkWeight_psiExt_free d n ψ ω)


theorem condFkProb_psiExt_eq_bcProb_free (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ (psiExt d n ψ ω)
      = bcProb (boxGraph d n) (inducedWiringFree d n ψ) p q ω := by
  rw [condFkProb_eq_inducedFkProb (boxGraph d (n+1)) hp hp1 hq, inducedFkProb,
    fkWeight_psiExt_free, inducedFkZ_innerEdgeFinset_psi_free, bcProb,
    mul_div_mul_right _ _ (psiShiftFree_pos hp hp1 hq).ne']


theorem sum_fibreMass_eq_one_free (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
        (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
          fkProb (boxGraph d (n+1)) p q σ) = 1 := by
  classical
  set F := innerEdgeFinset d n
  set G := boxGraph d (n+1)
  rw [show (∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
        (∑ σ ∈ condFibre F ψ, fkProb G p q σ))
      = ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
        (∑ σ ∈ Finset.univ.filter (fun ρ => outProj d n ρ = ψ), fkProb G p q σ) from ?_]
  · rw [Finset.sum_fiberwise_of_maps_to
        (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, outProj_idem n ρ⟩)]
    exact fkProb_sum_eq_one G hp hp1 hq
  · apply Finset.sum_congr rfl
    intro ψ hψ
    rw [Finset.mem_filter] at hψ
    rw [filter_outProj_eq_condFibre n ψ hψ.2]


theorem fkProb_eq_fibreMass_mul_condFkProb (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    fkProb (boxGraph d (n+1)) p q ω
      = (∑ ρ ∈ condFibre (innerEdgeFinset d n) ω, fkProb (boxGraph d (n+1)) p q ρ)
          * condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ω ω := by
  set G := boxGraph d (n+1)
  set F := innerEdgeFinset d n
  unfold condFkProb
  have hpos : 0 < ∑ ρ ∈ condFibre F ω, fkProb G p q ρ :=
    Finset.sum_pos (fun ρ _ => fkProb_pos G hp hp1 hq ρ) ⟨ω, self_mem_condFibre F ω⟩
  rw [mul_div_cancel₀ _ hpos.ne']


theorem condFkProb_congr_dom_free (n : ℕ) {p q : ℝ}
    (ψ ψ' ω : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (h : AgreesOff (innerEdgeFinset d n) ψ ψ') :
    condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ ω
      = condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ' ω := by
  unfold condFkProb
  have hfib : condFibre (innerEdgeFinset d n) ψ = condFibre (innerEdgeFinset d n) ψ' := by
    ext σ; rw [mem_condFibre, mem_condFibre, agreesOff_congr h]
  rw [hfib]


theorem freeSucc_fkProb_decompose (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (B : Set (ConfigSpace (Sym2 (boxVerts d (n+1))))) :
    (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * fkProb (boxGraph d (n+1)) p q ρ)
      = ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
          (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
            fkProb (boxGraph d (n+1)) p q σ)
          * (∑ ρ ∈ condFibre (innerEdgeFinset d n) ψ, B.indicator (fun _ => (1:ℝ)) ρ
              * condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ ρ) := by
  classical
  set F := innerEdgeFinset d n
  set G := boxGraph d (n+1)
  rw [← Finset.sum_fiberwise_of_maps_to
      (g := outProj d n) (t := Finset.univ.filter (fun ψ => outProj d n ψ = ψ))
      (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, outProj_idem n ρ⟩)]
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [Finset.mem_filter] at hψ
  rw [filter_outProj_eq_condFibre n ψ hψ.2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mem_condFibre] at hρ
  have hfk := fkProb_eq_fibreMass_mul_condFkProb n hp hp1 hq ρ
  have hfib : condFibre F ρ = condFibre F ψ := by
    ext σ; rw [mem_condFibre, mem_condFibre, agreesOff_congr (agreesOff_symm hρ)]
  rw [hfib] at hfk
  have hcc : condFkProb G p q F ρ ρ = condFkProb G p q F ψ ρ :=
    condFkProb_congr_dom_free n ρ ψ ρ (agreesOff_symm hρ)
  rw [hcc] at hfk
  rw [hfk]; ring


theorem condFkProb_psiExt_sum_eq_inducedBox_free (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (B : Set (ConfigSpace (Sym2 (boxVerts d (n+1))))) :
    (∑ ρ ∈ condFibre (innerEdgeFinset d n) ψ, B.indicator (fun _ => (1:ℝ)) ρ *
        condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ ρ)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (psiExt d n ψ ⁻¹' B).indicator (fun _ => (1:ℝ)) ω
            * bcProb (boxGraph d n) (inducedWiringFree d n ψ) p q ω := by
  classical
  rw [condFibre_eq_image_psiExt]
  rw [Finset.sum_image (fun a _ b _ h => by
    have := congrArg (innerRestrict d n) h
    rwa [innerRestrict_psiExt, innerRestrict_psiExt] at this)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [condFkProb_psiExt_eq_bcProb_free d n hp hp1 hq ψ ω]
  have hind : B.indicator (fun _ => (1:ℝ)) (psiExt d n ψ ω)
      = (psiExt d n ψ ⁻¹' B).indicator (fun _ => (1:ℝ)) ω := by
    by_cases hω : psiExt d n ψ ω ∈ B
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun h => hω (Set.mem_preimage.mp h))]
  rw [hind]


theorem fkProb_le_inducedFree (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA₀ : IsIncreasing A₀) :
    (∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p q ω)
      ≤ ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω
          * bcProb (boxGraph d n) (inducedWiringFree d n ψ) p q ω := by
  have hbot : (∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p q ω)
      = ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω
          * bcProb (boxGraph d n) (⊥ : SimpleGraph (boxVerts d n)) p q ω := by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    congr 1
    unfold fkProb bcProb fkZ bcZ
    rw [fkWeight, bcWeight, numClustersBC_bot]
    congr 1
    exact Finset.sum_congr rfl (fun ω _ => by rw [fkWeight, bcWeight, numClustersBC_bot])
  rw [hbot]
  exact bcProb_mono_bc (boxGraph d n) (⊥ : SimpleGraph (boxVerts d n))
    (inducedWiringFree d n ψ) bot_le hp hp1 hq hA₀


theorem fkProb_le_condFkProb_innerRestrict_free (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA₀ : IsIncreasing A₀) :
    (∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p q ω)
      ≤ ∑ ρ ∈ condFibre (innerEdgeFinset d n) ψ,
          (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ
            * condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ ρ := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  rw [condFkProb_psiExt_sum_eq_inducedBox_free d n hp hp1 hq0 ψ (innerRestrict d n ⁻¹' A₀)]
  have hpre : psiExt d n ψ ⁻¹' (innerRestrict d n ⁻¹' A₀) = A₀ := by
    ext ω
    simp only [Set.mem_preimage, innerRestrict_psiExt]
  rw [hpre]
  exact fkProb_le_inducedFree d n hp hp1 hq ψ hA₀


theorem freeSucc_fkProb_innerEvent_le (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA₀ : IsIncreasing A₀) :
    (∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p q ω)
      ≤ ∑ ρ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ
          * fkProb (boxGraph d (n+1)) p q ρ := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  set c := ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p q ω with hc
  rw [freeSucc_fkProb_decompose n hp hp1 hq0 (innerRestrict d n ⁻¹' A₀)]
  calc c = c * 1 := (mul_one c).symm
    _ = c * ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
          (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ, fkProb (boxGraph d (n+1)) p q σ) := by
          rw [sum_fibreMass_eq_one_free n hp hp1 hq0]
    _ = ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
          (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ, fkProb (boxGraph d (n+1)) p q σ) * c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ψ _ => mul_comm _ _)
    _ ≤ ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
          (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ, fkProb (boxGraph d (n+1)) p q σ)
            * (∑ ρ ∈ condFibre (innerEdgeFinset d n) ψ,
                (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ
                  * condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ ρ) := by
          apply Finset.sum_le_sum
          intro ψ _
          apply mul_le_mul_of_nonneg_left
            (fkProb_le_condFkProb_innerRestrict_free d n hp hp1 hq ψ hA₀)
          exact Finset.sum_nonneg (fun σ _ => (fkProb_pos (boxGraph d (n+1)) hp hp1 hq0 σ).le)


theorem freeFiniteMeasure_real_boxRestrictEvent (m : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (S : Set (ConfigSpace (Sym2 (boxVerts d m))))
    (hmeas : MeasurableSet (boxRestrict d m ⁻¹' S)) :
    (freeFiniteMeasure d m hp hp1 hq
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d m)),
          S.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d m) p q ω := by
  have hf : (freeFiniteMeasure d m hp hp1 hq : Measure _).real (boxRestrict d m ⁻¹' S)
      = ((fkPMF (boxGraph d m) hp hp1 hq).toMeasure
          (extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S))).toReal := by
    unfold freeFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d m) hmeas]
  have hpre : extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S) = S := by
    ext ω
    simp only [Set.mem_preimage, boxRestrict_extendEdge]
  rw [hf, hpre, fkPMF_toMeasure_toReal d m hp hp1 hq]


theorem freeFiniteMeasure_succ_real_innerRestrictEvent (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 (boxVerts d n))))
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (freeFiniteMeasure d (n+1) hp hp1 hq
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S)
      = ∑ ρ : ConfigSpace (Sym2 (boxVerts d (n+1))),
          (innerRestrict d n ⁻¹' S).indicator (fun _ => (1:ℝ)) ρ
            * fkProb (boxGraph d (n+1)) p q ρ := by
  have hf : (freeFiniteMeasure d (n+1) hp hp1 hq : Measure _).real (boxRestrict d n ⁻¹' S)
      = ((fkPMF (boxGraph d (n+1)) hp hp1 hq).toMeasure
          (extendEdge d (n+1) ⁻¹' (boxRestrict d n ⁻¹' S))).toReal := by
    unfold freeFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d (n+1)) hmeas]
  have hpre : extendEdge d (n+1) ⁻¹' (boxRestrict d n ⁻¹' S) = innerRestrict d n ⁻¹' S := by
    ext ρ
    simp only [Set.mem_preimage, boxRestrict_extendEdge_succ]
  rw [hf, hpre, fkPMF_toMeasure_toReal d (n+1) hp hp1 hq]


theorem freeFiniteMeasure_smallerBox_le_succ (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hS : IsIncreasing S)
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (∑ ω, S.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p 2 ω)
      ≤ (freeFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S) := by
  rw [freeFiniteMeasure_succ_real_innerRestrictEvent n hp hp1 (by norm_num) S hmeas]
  exact freeSucc_fkProb_innerEvent_le n hp hp1 (by norm_num) hS


theorem fkFreeLimit_isIncreasing_preimage (N : ℕ)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    IsIncreasing (boxRestrict d N ⁻¹' S) :=
  fun _ _ hab ha => hS (monotone_boxRestrict d N hab) ha


theorem fkFreeLimit_isClopen_preimage (N : ℕ) (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    IsClopen (boxRestrict d N ⁻¹' S) :=
  IsClopen.preimage ⟨isClosed_discrete _, isOpen_discrete _⟩ (continuous_boxRestrict d N)


theorem fkFreeLimit_measurableSet_preimage (N : ℕ)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    MeasurableSet (boxRestrict d N ⁻¹' S) :=
  (fkFreeLimit_isClopen_preimage N S).isOpen.measurableSet


theorem fkFreeLimit_le_succ (N m : ℕ) (hNm : N ≤ m) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ (freeFiniteMeasure d (m+1) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  set T := boxRestrictLE d hNm ⁻¹' S with hT
  have hTinc : IsIncreasing T := fun a b hab ha => hS (boxRestrictLE_monotone d hNm hab) ha
  have heq : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [heq, freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (by norm_num) T hmeas]
  exact freeFiniteMeasure_smallerBox_le_succ m hp hp1 hTinc hmeas


theorem fkFreeLimit_monotone (N : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Monotone (fun k => (freeFiniteMeasure d (N+k) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) := by
  apply monotone_nat_of_le_succ
  intro k
  have h := fkFreeLimit_le_succ N (N+k) (Nat.le_add_right N k) hp hp1 hS
  rw [show N + (k+1) = (N+k)+1 from by ring]
  exact h


end FK
end StatMech
