import Mathlib

open MeasureTheory Set
open scoped MatrixGroups Pointwise NNReal ENNReal

noncomputable section

namespace FLT.HyperbolicMeasure

open UpperHalfPlane

example : MeasureSpace ℍ := inferInstance

example : SigmaFinite (volume : Measure ℍ) := inferInstance

example : SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ volume := inferInstance

example : IsFiniteMeasureOnCompacts (volume : Measure ℍ) := inferInstance

theorem volume_smul_gl (g : GL (Fin 2) ℝ) (s : Set ℍ) : volume (g • s) = volume s :=
  MeasureTheory.measure_smul (volume : Measure ℍ) g s

instance : SMulInvariantMeasure SL(2, ℤ) ℍ (volume : Measure ℍ) where
  measure_preimage_smul g s hs := by

    simp only [MulAction.compHom_smul_def]
    exact SMulInvariantMeasure.measure_preimage_smul (Matrix.SpecialLinearGroup.mapGL ℝ g) hs

theorem volume_smul_sl2z (γ : SL(2, ℤ)) (s : Set ℍ) : volume (γ • s) = volume s :=
  MeasureTheory.measure_smul (volume : Measure ℍ) γ s

private lemma measurable_density :
    Measurable fun z : ℂ => ((((1 : ℝ≥0) / ‖z.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  fun_prop

private lemma density_ne_zero {w : ℂ} (hw : w ∈ Set.range (UpperHalfPlane.coe)) :
    ((((1 : ℝ≥0) / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
  obtain ⟨τ, rfl⟩ := hw
  have him : (τ : ℂ).im ≠ 0 := ne_of_gt τ.2
  simp only [ne_eq, ENNReal.coe_eq_zero, pow_eq_zero_iff, OfNat.ofNat_ne_zero,
    not_false_eq_true, div_eq_zero_iff, one_ne_zero, nnnorm_eq_zero, false_or]
  exact him

instance : Measure.IsOpenPosMeasure (volume : Measure ℍ) := by
  constructor
  intro U hU hUne

  rw [UpperHalfPlane.volume_eq_lintegral]

  have himage_open : IsOpen (UpperHalfPlane.coe '' U) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hU
  have himage_ne : (UpperHalfPlane.coe '' U).Nonempty := hUne.image _
  have hpos : 0 < volume (UpperHalfPlane.coe '' U) :=
    himage_open.measure_pos volume himage_ne

  refine ((MeasureTheory.setLIntegral_pos_iff measurable_density).mpr ?_).ne'
  refine hpos.trans_le (measure_mono fun w hw => ?_)
  exact ⟨density_ne_zero (Set.image_subset_range _ _ hw), hw⟩

theorem volume_pos_of_isOpen {U : Set ℍ} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < volume U :=
  hU.measure_pos _ hne

private def box (n : ℤ) : Set ℍ :=
  UpperHalfPlane.re ⁻¹' Set.Ioo (n : ℝ) (n + 1) ∩ UpperHalfPlane.im ⁻¹' Set.Ioo (1 : ℝ) 2

private lemma isOpen_box (n : ℤ) : IsOpen (box n) :=
  (isOpen_Ioo.preimage UpperHalfPlane.continuous_re).inter
    (isOpen_Ioo.preimage UpperHalfPlane.continuous_im)

private lemma box_nonempty (n : ℤ) : (box n).Nonempty := by
  refine ⟨UpperHalfPlane.mk ⟨(n : ℝ) + 1 / 2, 3 / 2⟩ (by norm_num), ?_, ?_⟩ <;>
      simp only [Set.mem_preimage, UpperHalfPlane.mk_re, UpperHalfPlane.mk_im, Set.mem_Ioo]
  · exact ⟨by norm_num, by norm_num⟩
  · exact ⟨by norm_num, by norm_num⟩

private lemma pairwise_disjoint_box : Pairwise (Function.onFun Disjoint box) := by
  intro m n hmn
  refine Set.disjoint_left.mpr fun z hzm hzn => hmn ?_
  have h1 : (m : ℝ) < z.re ∧ z.re < m + 1 := hzm.1
  have h2 : (n : ℝ) < z.re ∧ z.re < n + 1 := hzn.1

  have : (m : ℝ) = n := by
    rcases lt_trichotomy m n with h | h | h
    · exfalso
      have : (m : ℝ) + 1 ≤ n := by exact_mod_cast Int.add_one_le_of_lt h
      linarith [h1.2, h2.1]
    · exact_mod_cast h
    · exfalso
      have : (n : ℝ) + 1 ≤ m := by exact_mod_cast Int.add_one_le_of_lt h
      linarith [h2.2, h1.1]
  exact_mod_cast this

private lemma box_eq_smul (n : ℤ) : box n = (ModularGroup.T ^ n) • box 0 := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem, ← zpow_neg]
  simp only [box, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioo,
    ModularGroup.re_T_zpow_smul, ModularGroup.im_T_zpow_smul, Int.cast_neg, Int.cast_zero]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, by linarith⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, by linarith⟩, h3⟩

theorem volume_univ_eq_top : volume (Set.univ : Set ℍ) = ⊤ := by

  have hdisj := pairwise_disjoint_box
  have hmeas : ∀ n : ℤ, MeasurableSet (box n) := fun n => (isOpen_box n).measurableSet
  have hsum : volume (⋃ n : ℤ, box n) = ∑' n : ℤ, volume (box n) :=
    measure_iUnion hdisj hmeas

  have hconst : ∀ n : ℤ, volume (box n) = volume (box 0) := fun n => by
    rw [box_eq_smul n, volume_smul_sl2z]
  have hpos : volume (box 0) ≠ 0 :=
    (volume_pos_of_isOpen (isOpen_box 0) (box_nonempty 0)).ne'

  have htop : volume (⋃ n : ℤ, box n) = ⊤ := by
    rw [hsum]
    calc ∑' n : ℤ, volume (box n) = ∑' _ : ℤ, volume (box 0) := by
          exact tsum_congr hconst
      _ = ⊤ := ENNReal.tsum_const_eq_top_of_ne_zero hpos
  exact eq_top_mono (measure_mono (Set.subset_univ _)) htop

theorem not_isFiniteMeasure_volume : ¬ IsFiniteMeasure (volume : Measure ℍ) := by
  intro h
  exact (measure_lt_top (volume : Measure ℍ) Set.univ).ne volume_univ_eq_top

end FLT.HyperbolicMeasure
end
