import Mathlib
import Lemma.Definitions.Def_AutomorphicForm_HyperbolicMeasure

open MeasureTheory Set ModularGroup UpperHalfPlane
open scoped MatrixGroups Modular Pointwise NNReal ENNReal

noncomputable section

namespace FLT.FundamentalDomainVolume

def band (A a : ℝ) (n : ℕ) : Set ℍ :=
  {z : ℍ | |z.re| ≤ A ∧ a * 2 ^ n ≤ z.im ∧ z.im ≤ a * 2 ^ (n + 1)}

theorem verticalStrip_subset_iUnion_band (A : ℝ) {a : ℝ} (ha : 0 < a) :
    UpperHalfPlane.verticalStrip A a ⊆ ⋃ n : ℕ, band A a n := by
  rintro z ⟨hre, him⟩

  have hex : ∃ n : ℕ, z.im ≤ a * 2 ^ (n + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (z.im / a) (one_lt_two (α := ℝ))
    exact ⟨n, by
      rw [div_lt_iff₀ ha] at hn
      nlinarith [pow_pos (zero_lt_two (α := ℝ)) n, pow_succ (2 : ℝ) n]⟩
  classical

  refine Set.mem_iUnion.mpr ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · exact hre

  rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hex) with h0 | hsucc
  · rw [h0]; simpa using him
  · rw [hsucc]
    have hlt := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    rw [not_le] at hlt
    exact le_of_lt hlt

private def cbox (relo rehi imlo imhi : ℝ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Set.Icc relo rehi ×ˢ Set.Icc imlo imhi)

private lemma mem_cbox {relo rehi imlo imhi : ℝ} {w : ℂ} :
    w ∈ cbox relo rehi imlo imhi ↔
      (relo ≤ w.re ∧ w.re ≤ rehi) ∧ imlo ≤ w.im ∧ w.im ≤ imhi := by
  simp only [cbox, Set.mem_preimage, Complex.measurableEquivRealProd_apply, Set.mem_prod,
    Set.mem_Icc]

private lemma volume_cbox (relo rehi imlo imhi : ℝ) :
    volume (cbox relo rehi imlo imhi) =
      ENNReal.ofReal (rehi - relo) * ENNReal.ofReal (imhi - imlo) := by
  rw [cbox, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet)]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]

theorem volume_band_le {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (n : ℕ) :
    volume (band A a n) ≤ ENNReal.ofReal (2 * A * (a⁻¹ * (1 / 2) ^ n)) := by
  have h2n : (0 : ℝ) < a * 2 ^ n := by positivity

  rw [UpperHalfPlane.volume_eq_lintegral]

  have himg : (UpperHalfPlane.coe '' band A a n) ⊆
      cbox (-A) A (a * 2 ^ n) (a * 2 ^ (n + 1)) := by
    rintro w ⟨z, ⟨hre, him₁, him₂⟩, rfl⟩
    rw [mem_cbox, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    exact ⟨abs_le.mp hre, him₁, him₂⟩
  refine le_trans (lintegral_mono_set himg) ?_

  have hbound : ∀ w ∈ cbox (-A) A (a * 2 ^ n) (a * 2 ^ (n + 1)),
      (((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal ((a * 2 ^ n)⁻¹ ^ 2) := by
    intro w hw
    obtain ⟨-, him₁, -⟩ := mem_cbox.mp hw
    have hwim : (0 : ℝ) < w.im := lt_of_lt_of_le h2n him₁
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    rw [Real.norm_eq_abs, abs_of_pos hwim]
    have : (a * 2 ^ n)⁻¹ ^ 2 = (1 / (a * 2 ^ n)) ^ 2 := by rw [one_div]
    rw [this]
    gcongr
  refine le_trans (setLIntegral_mono measurable_const hbound) ?_

  rw [setLIntegral_const, volume_cbox]
  have harith₁ : A - -A = 2 * A := by ring
  have harith₂ : a * 2 ^ (n + 1) - a * 2 ^ n = a * 2 ^ n := by ring
  rw [harith₁, harith₂, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [show (a * 2 ^ n)⁻¹ ^ 2 * (2 * A * (a * 2 ^ n)) =
        2 * A * ((a * 2 ^ n)⁻¹ ^ 2 * (a * 2 ^ n)) by ring,
    pow_two, mul_assoc ((a * 2 ^ n)⁻¹), inv_mul_cancel₀ h2n.ne', mul_one, mul_inv,
    ← inv_pow]
  norm_num

theorem volume_verticalStrip_lt_top (A : ℝ) {a : ℝ} (ha : 0 < a) :
    volume (UpperHalfPlane.verticalStrip A a) < ⊤ := by

  rcases le_or_gt 0 A with hA | hA
  swap
  · have hempty : UpperHalfPlane.verticalStrip A a = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hz
      exact absurd hz.1 (not_le.mpr (lt_of_lt_of_le hA (abs_nonneg _)))
    rw [hempty]
    simp
  calc volume (UpperHalfPlane.verticalStrip A a)
      ≤ volume (⋃ n : ℕ, band A a n) :=
        measure_mono (verticalStrip_subset_iUnion_band A ha)
    _ ≤ ∑' n : ℕ, volume (band A a n) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (2 * A * (a⁻¹ * (1 / 2) ^ n)) :=
        ENNReal.tsum_le_tsum fun n => volume_band_le hA ha n
    _ = ∑' n : ℕ, ENNReal.ofReal (2 * A * a⁻¹) * ENNReal.ofReal ((1 / 2) ^ n) :=
        tsum_congr fun n => by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
    _ = ENNReal.ofReal (2 * A * a⁻¹) * ∑' n : ℕ, ENNReal.ofReal ((1 / 2) ^ n) :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (2 * A * a⁻¹) * ∑' n : ℕ, ENNReal.ofReal (1 / 2) ^ n :=
        congrArg _ (tsum_congr fun n => ENNReal.ofReal_pow (by norm_num) n)
    _ = ENNReal.ofReal (2 * A * a⁻¹) * (1 - ENNReal.ofReal (1 / 2))⁻¹ := by
        rw [ENNReal.tsum_geometric]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [ENNReal.inv_lt_top, tsub_pos_iff_lt]
        exact ENNReal.ofReal_lt_one.mpr (by norm_num)

theorem fd_subset_verticalStrip : 𝒟 ⊆ UpperHalfPlane.verticalStrip (1 / 2) (1 / 2) := by
  intro z hz
  refine ⟨hz.2, ?_⟩
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  nlinarith [z.im_pos]

theorem volume_fd_lt_top : volume 𝒟 < ⊤ :=
  lt_of_le_of_lt (measure_mono fd_subset_verticalStrip)
    (volume_verticalStrip_lt_top (1 / 2) (by norm_num))

theorem volume_biUnion_smul_fd_lt_top (S : Finset SL(2, ℤ)) :
    volume (⋃ γ ∈ S, γ • 𝒟) < ⊤ := by
  refine lt_of_le_of_lt (measure_biUnion_finset_le S _) ?_
  rw [ENNReal.sum_lt_top]
  intro γ _
  rw [FLT.HyperbolicMeasure.volume_smul_sl2z]
  exact volume_fd_lt_top

private def fdoWitness : ℍ := UpperHalfPlane.mk ⟨0, 2⟩ (by norm_num)

private lemma fdoWitness_mem_fdo : fdoWitness ∈ 𝒟ᵒ := by
  constructor
  · show 1 < Complex.normSq (fdoWitness : ℂ)
    norm_num [fdoWitness, Complex.normSq_apply, UpperHalfPlane.coe_mk]
  · show |fdoWitness.re| < 1 / 2
    norm_num [fdoWitness, UpperHalfPlane.mk_re]

theorem volume_fd_pos : 0 < volume 𝒟 :=
  lt_of_lt_of_le
    (FLT.HyperbolicMeasure.volume_pos_of_isOpen ModularGroup.isOpen_fdo
      ⟨fdoWitness, fdoWitness_mem_fdo⟩)
    (measure_mono ModularGroup.fdo_subset_fd)

theorem volume_fd_lt_volume_univ : volume 𝒟 < volume (Set.univ : Set ℍ) := by
  rw [FLT.HyperbolicMeasure.volume_univ_eq_top]
  exact volume_fd_lt_top

theorem volume_fd_ne_zero_ne_top : volume 𝒟 ≠ 0 ∧ volume 𝒟 ≠ ⊤ :=
  ⟨volume_fd_pos.ne', volume_fd_lt_top.ne⟩

example : volume ((1 : SL(2, ℤ)) • 𝒟 ∪ ModularGroup.S • 𝒟) < ⊤ := by
  have := volume_biUnion_smul_fd_lt_top {1, ModularGroup.S}
  refine lt_of_le_of_lt (measure_mono ?_) this
  intro z hz
  rcases hz with hz | hz
  · exact Set.mem_biUnion (Finset.mem_insert_self _ _) hz
  · exact Set.mem_biUnion (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hz

example : volume (⋃ γ ∈ (∅ : Finset SL(2, ℤ)), γ • 𝒟) < ⊤ := by
  simp

end FLT.FundamentalDomainVolume

end
