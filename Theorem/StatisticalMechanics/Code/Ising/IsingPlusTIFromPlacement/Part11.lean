/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Def.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

open StatMech.Percolation

variable {d : ℕ}


theorem iptp_gvBondTouch_image_subset (g : Multiplicative (Site d)) (S : Finset (Site d)) :
    (gvBondTouch S).image (fun e => g • e) ⊆ gvBondTouch (S.image (fun x => g • x)) := by
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨e0, he0, rfl⟩ := he
  rw [gvBondTouch, Finset.mem_image] at he0
  obtain ⟨p, hp, rfl⟩ := he0
  rw [Finset.mem_filter] at hp
  obtain ⟨_, hadj, htouch⟩ := hp
  rw [smul_sym2_mk]
  refine gv_mk_mem_bondTouch ((hyper_adj_smul g p.1 p.2).mpr hadj) ?_
  rcases htouch with h | h
  · exact Or.inl (Finset.mem_image_of_mem _ h)
  · exact Or.inr (Finset.mem_image_of_mem _ h)


theorem iptp_gvBondTouch_image (g : Multiplicative (Site d)) (S : Finset (Site d)) :
    gvBondTouch (S.image (fun x => g • x)) = (gvBondTouch S).image (fun e => g • e) := by
  apply Finset.Subset.antisymm _ (iptp_gvBondTouch_image_subset g S)
  have hfwd := iptp_gvBondTouch_image_subset g⁻¹ (S.image (fun x => g • x))
  intro e he
  have hmem : (g⁻¹ • e) ∈ gvBondTouch ((S.image (fun x => g • x)).image (fun x => g⁻¹ • x)) :=
    hfwd (Finset.mem_image_of_mem _ he)
  rw [Finset.image_image] at hmem
  have hcomp : ((fun x : Site d => g⁻¹ • x) ∘ fun x : Site d => g • x) = id := by
    funext x; exact inv_smul_smul g x
  rw [hcomp, Finset.image_id] at hmem
  rw [Finset.mem_image]
  exact ⟨g⁻¹ • e, hmem, by rw [smul_inv_smul]⟩


theorem iptp_gvGlue_shift (g : Multiplicative (Site d)) (S : Finset (Site d))
    (τ : {x // x ∈ S} → Bool) :
    ConfigSpace.shift g (gvGlue (plusField d) S τ)
      = gvGlue (plusField d) (S.image (fun x => g • x))
          (fun y => τ ((iptp_transInteriorEquiv g S).symm y)) := by
  funext x
  rw [ConfigSpace.shift_apply]
  by_cases hx : x ∈ S.image (fun x => g • x)
  · have hinv : g⁻¹ • x ∈ S := by
      obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hx; rw [← hzeq, inv_smul_smul]; exact hz
    rw [gvGlue_mem _ _ _ hx, gvGlue_mem _ _ _ hinv]; congr 1
  · have hinv : g⁻¹ • x ∉ S := by
      intro hc; exact hx (by rw [← smul_inv_smul g x]; exact Finset.mem_image_of_mem _ hc)
    rw [gvGlue_not_mem _ _ _ hx, gvGlue_not_mem _ _ _ hinv]; simp [plusField]


theorem iptp_spin_shift (g : Multiplicative (Site d)) (c : ConfigSpace (Site d)) (x : Site d) :
    spin (ConfigSpace.shift g c) (g • x) = spin c x := by
  unfold spin; rw [ConfigSpace.shift_apply, inv_smul_smul]


theorem iptp_bond_shift (g : Multiplicative (Site d)) (c : ConfigSpace (Site d)) (e : Sym2 (Site d)) :
    bond (ConfigSpace.shift g c) (g • e) = bond c e := by
  induction e with
  | h x y => rw [smul_sym2_mk, bond_mk, bond_mk, iptp_spin_shift, iptp_spin_shift]


theorem iptp_gvEnergy_shift (g : Multiplicative (Site d)) (S : Finset (Site d)) (h : ℝ)
    (τ : {x // x ∈ S} → Bool) :
    gvEnergy (plusField d) (S.image (fun x => g • x)) h
        (fun y => τ ((iptp_transInteriorEquiv g S).symm y))
      = gvEnergy (plusField d) S h τ := by
  unfold gvEnergy
  rw [← iptp_gvGlue_shift g S τ]
  congr 1
  · rw [iptp_gvBondTouch_image,
      Finset.sum_image (fun a _ b _ hab => MulAction.injective g hab)]
    congr 1
    exact Finset.sum_congr rfl (fun e _ => iptp_bond_shift g (gvGlue (plusField d) S τ) e)
  · congr 1
    rw [Finset.sum_image (fun a _ b _ hab => MulAction.injective g hab)]
    exact Finset.sum_congr rfl (fun x _ => iptp_spin_shift g (gvGlue (plusField d) S τ) x)

theorem iptp_gvWeight_shift (g : Multiplicative (Site d)) (S : Finset (Site d)) (β h : ℝ)
    (τ : {x // x ∈ S} → Bool) :
    gvWeight (plusField d) (S.image (fun x => g • x)) β h
        (fun y => τ ((iptp_transInteriorEquiv g S).symm y))
      = gvWeight (plusField d) S β h τ := by
  unfold gvWeight; rw [iptp_gvEnergy_shift]

theorem iptp_gvZ_shift (g : Multiplicative (Site d)) (S : Finset (Site d)) (β h : ℝ) :
    gvZ (plusField d) (S.image (fun x => g • x)) β h = gvZ (plusField d) S β h := by
  unfold gvZ
  rw [← Equiv.sum_comp (Equiv.arrowCongr (iptp_transInteriorEquiv g S) (Equiv.refl Bool))
    (fun τ => gvWeight (plusField d) (S.image (fun x => g • x)) β h τ)]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [← iptp_gvWeight_shift g S β h τ]; rfl

theorem iptp_gvProb_shift (g : Multiplicative (Site d)) (S : Finset (Site d)) (β h : ℝ)
    (τ : {x // x ∈ S} → Bool) :
    gvProb (plusField d) (S.image (fun x => g • x)) β h
        (fun y => τ ((iptp_transInteriorEquiv g S).symm y))
      = gvProb (plusField d) S β h τ := by
  unfold gvProb; rw [iptp_gvWeight_shift, iptp_gvZ_shift]

theorem iptp_map_sum_aux {ι : Type*} [Fintype ι] (f : ConfigSpace (Site d) → ConfigSpace (Site d))
    (hf : Measurable f) (μ : ι → Measure (ConfigSpace (Site d))) :
    Measure.map f (∑ i, μ i) = ∑ i, Measure.map f (μ i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hf, ih]


theorem iptp_gvMeasure_map_shift (g : Multiplicative (Site d)) (S : Finset (Site d)) (β h : ℝ) :
    Measure.map (ConfigSpace.shift g) (gvMeasure (plusField d) S β h)
      = gvMeasure (plusField d) (S.image (fun x => g • x)) β h := by
  unfold gvMeasure
  rw [iptp_map_sum_aux _ (ConfigSpace.measurable_shift g)]
  rw [← Equiv.sum_comp (Equiv.arrowCongr (iptp_transInteriorEquiv g S) (Equiv.refl Bool))
    (fun τ => ENNReal.ofReal (gvProb (plusField d) (S.image (fun x => g • x)) β h τ)
      • Measure.dirac (gvGlue (plusField d) (S.image (fun x => g • x)) τ))]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Measure.map_smul, Measure.map_dirac (gvGlue (plusField d) S τ)]
  rw [show gvProb (plusField d) (S.image (fun x => g • x)) β h
        ((Equiv.arrowCongr (iptp_transInteriorEquiv g S) (Equiv.refl Bool)) τ)
        = gvProb (plusField d) S β h τ from iptp_gvProb_shift g S β h τ,
    show gvGlue (plusField d) (S.image (fun x => g • x))
        ((Equiv.arrowCongr (iptp_transInteriorEquiv g S) (Equiv.refl Bool)) τ)
        = ConfigSpace.shift g (gvGlue (plusField d) S τ) from (iptp_gvGlue_shift g S τ).symm]


theorem iptp_gvPlus_real_shift (g : Multiplicative (Site d)) (S : Finset (Site d)) (β h : ℝ)
    (T : Finset (Site d)) :
    (gvPlusMeasure (S.image (fun x => g • x)) β h).real (fmu_multiOpen T)
      = (gvPlusMeasure S β h).real (fmu_multiOpen (T.image (fun e => g⁻¹ • e))) := by
  rw [gvPlusMeasure, gvPlusMeasure, ← iptp_gvMeasure_map_shift g S β h, Measure.real,
    Measure.map_apply (ConfigSpace.measurable_shift g) (fmu_multiOpen_measurable T),
    ← fmu_shift_multiOpen g T]
  rfl


theorem iptp_inv_smul_coord (g : Multiplicative (Site d)) (y : Site d) (i : Fin d) :
    (g⁻¹ • y) i = y i - Multiplicative.toAdd g i := by
  rw [smul_site_apply, show Multiplicative.toAdd g⁻¹ = - Multiplicative.toAdd g from rfl]
  simp; ring


theorem iptp_box_subset_transBox (g : Multiplicative (Site d)) {a m : ℕ}
    (hcm : a + flc_vrad (Multiplicative.toAdd g) ≤ m) :
    boxFinset d a ⊆ (boxFinset d m).image (fun x => g • x) := by
  intro y hy
  rw [Finset.mem_image]
  refine ⟨g⁻¹ • y, mem_boxFinset.mpr ?_, by rw [smul_inv_smul]⟩
  intro i
  have hyi : (y i).natAbs ≤ a := mem_boxFinset.mp hy i
  have hvi : (Multiplicative.toAdd g i).natAbs ≤ flc_vrad (Multiplicative.toAdd g) := flc_vrad_le _ i
  rw [iptp_inv_smul_coord g y i]
  calc (y i - Multiplicative.toAdd g i).natAbs
        ≤ (y i).natAbs + (Multiplicative.toAdd g i).natAbs := Int.natAbs_sub_le _ _
    _ ≤ a + flc_vrad (Multiplicative.toAdd g) := Nat.add_le_add hyi hvi
    _ ≤ m := hcm


theorem iptp_transBox_subset_box (g : Multiplicative (Site d)) (m : ℕ) :
    (boxFinset d m).image (fun x => g • x) ⊆ boxFinset d (m + flc_vrad (Multiplicative.toAdd g)) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  rw [mem_boxFinset]
  intro i
  have hzi : (z i).natAbs ≤ m := mem_boxFinset.mp hz i
  have hvi : (Multiplicative.toAdd g i).natAbs ≤ flc_vrad (Multiplicative.toAdd g) := flc_vrad_le _ i
  have hgz : (g • z) i = Multiplicative.toAdd g i + z i := smul_site_apply g z i
  rw [hgz]
  calc (Multiplicative.toAdd g i + z i).natAbs
        ≤ (Multiplicative.toAdd g i).natAbs + (z i).natAbs := Int.natAbs_add_le _ _
    _ ≤ flc_vrad (Multiplicative.toAdd g) + m := Nat.add_le_add hvi hzi
    _ = m + flc_vrad (Multiplicative.toAdd g) := by omega


theorem iptp_squeeze_lower {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (g : Multiplicative (Site d)) (T : Finset (Site d)) (m : ℕ) :
    (plusMeasure d (m + flc_vrad (Multiplicative.toAdd g)) β h
        : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T)
      ≤ (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x))) := by
  
  rw [← iptp_gvPlusMeasure_eq_plusMeasure m β h, ← iptp_gvPlus_real_shift g (boxFinset d m) β h T,
    ← iptp_gvPlusMeasure_eq_plusMeasure (m + flc_vrad (Multiplicative.toAdd g)) β h]
  
  exact iptp_gv_crossbox_dom (iptp_transBox_subset_box g m) hβ hh
    (IsClopen.measurableSet_configSpace (ipe_multiOpen_isClopen T)) (fmu_multiOpen_isIncreasing T)


theorem iptp_squeeze_upper {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (g : Multiplicative (Site d)) (T : Finset (Site d)) {a m : ℕ}
    (hcond : a + flc_vrad (Multiplicative.toAdd g) ≤ m) :
    (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x)))
      ≤ (plusMeasure d a β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen (E := Site d) T) := by
  rw [← iptp_gvPlusMeasure_eq_plusMeasure m β h, ← iptp_gvPlusMeasure_eq_plusMeasure a β h,
    ← iptp_gvPlus_real_shift g (boxFinset d m) β h T]
  exact iptp_gv_crossbox_dom (iptp_box_subset_transBox g hcond) hβ hh
    (IsClopen.measurableSet_configSpace (ipe_multiOpen_isClopen T)) (fmu_multiOpen_isIncreasing T)


theorem iptp_plusMultiHomogeneous {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (g : Multiplicative (Site d)) : iti_PlusMultiHomogeneous β h g := by
  intro T
  obtain ⟨φ, hφ, hconv⟩ := plusState_isInfiniteVolumeState d β h
  set c := flc_vrad (Multiplicative.toAdd g) with hc
  set IV_T := (plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T)
    with hivt
  set IV_T' := (plusState d β h : Measure (ConfigSpace (Site d))).real
    (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x))) with hivt'
  
  have hmid : Tendsto (fun m => (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x)))) atTop (𝓝 IV_T') :=
    itb_plus_multiOpen_full_tendsto hβ hh (T.image (fun x => g⁻¹ • x)) hφ hconv
  
  have hfull : Tendsto (fun m => (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T)) atTop (𝓝 IV_T) :=
    itb_plus_multiOpen_full_tendsto hβ hh T hφ hconv
  
  have hup : Tendsto (fun m => (plusMeasure d (m + c) β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T)) atTop (𝓝 IV_T) := hfull.comp (tendsto_add_atTop_nat c)
  have hlow : Tendsto (fun m => (plusMeasure d (m - c) β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T)) atTop (𝓝 IV_T) := hfull.comp (tendsto_sub_atTop_nat c)
  
  have hle1 : IV_T ≤ IV_T' :=
    le_of_tendsto_of_tendsto hup hmid
      (Filter.Eventually.of_forall (fun m => iptp_squeeze_lower hβ hh g T m))
  
  have hle2 : IV_T' ≤ IV_T := by
    refine le_of_tendsto_of_tendsto hmid hlow ?_
    filter_upwards [Filter.eventually_ge_atTop c] with m hm
    exact iptp_squeeze_upper hβ hh g T (by omega : (m - c) + c ≤ m)
  exact le_antisymm hle1 hle2


theorem iptp_plusState_isTranslationInvariant {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  iti_plusState_isTranslationInvariant_of_homogeneous β h
    (fun g => iptp_plusMultiHomogeneous hβ hh g)


theorem ising_plus_extreme (hd : 1 ≤ d) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h) :
    StatMech.FK.IsInvariantExtremePoint (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  icb_plusState_isInvariantExtremePoint hd hβ hh (iptp_plusState_isTranslationInvariant hβ hh)


theorem iptp_plusState_isErgodic (hd : 1 ≤ d) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h) :
    IsErgodic (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  icb_plusState_isErgodic hd hβ hh (iptp_plusState_isTranslationInvariant hβ hh)

end Ising
end StatMech
