import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.RandomProjection
open MeasureTheory Measure Real Set RandomProjection NearlyEquidistantPoints
open scoped ENNReal NNReal
open Real Set MeasureTheory


namespace RandomProjection

/--
[log2_lt_one_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/RandomProjection.lean)
-/
@[path]
lemma log2_lt_one_aux
-- imply
  Real.log 2 < 1 := by
-- proof
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (by norm_num) (by linarith [exp_one_gt_d9])

end RandomProjection

namespace RandomProjection

/--
[one_le_two_mul_exp_neg_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/RandomProjection.lean)
-/
@[path]
lemma one_le_two_mul_exp_neg_aux
  {r : ℝ}
-- given
  (hr : r ≤ Real.log 2) :
-- imply
  1 ≤ 2 * Real.exp (-r) := by
-- proof
  have h1 : Real.exp (-r) ≥ Real.exp (-(Real.log 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(Real.log 2)) = 1/2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (2:ℝ) > 0)]; norm_num
  linarith

end RandomProjection

namespace RandomProjection

/--
[tail_recenter_toReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/RandomProjection.lean)
-/
@[path]
lemma tail_recenter_toReal
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {m : ℕ}
  {Y : Ω → ℝ}
  {med center : ℝ}
-- given
  (hm : 0 < m)
  (hmed : ∀ s : ℝ, s ≥ 0 → (μ {ω | |Y ω - med| ≥ s}).toReal ≤ 2 * exp (-(↑m * s ^ 2) / 4)) :
-- imply
  ∃ c : ℝ, c > 0 ∧ ∀ t : ℝ, t ≥ 0 → (μ {ω | |Y ω - center| ≥ t}).toReal ≤ 2 * exp (-c * ↑m * t ^ 2) := by
-- proof
  have hm_pos : (0:ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hlog2_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set δ := |med - center|
  have hD_pos : (0:ℝ) < 16 + 16 * ↑m * (δ + 1) ^ 2 := by positivity
  set c := Real.log 2 / (16 + 16 * ↑m * (δ + 1) ^ 2)
  have hc_pos : (0:ℝ) < c := div_pos hlog2_pos hD_pos
  have hc_le : c ≤ 1 / 16 := by
    rw [div_le_div_iff₀ hD_pos (by norm_num : (0:ℝ) < 16)]
    nlinarith [log2_lt_one_aux, sq_nonneg (δ + 1), hm_pos]
  have hsmall_bound : ∀ t : ℝ, 0 ≤ t → t < 2 * (δ + 1) →
    c * ↑m * t ^ 2 ≤ Real.log 2 := by
    intro t ht ht_lt
    have ht2 : t ^ 2 ≤ (2 * (δ + 1)) ^ 2 := sq_le_sq' (by linarith) (le_of_lt ht_lt)
    have h1 : c * ↑m * t ^ 2 ≤ c * ↑m * (2 * (δ + 1)) ^ 2 := by
      have := mul_le_mul_of_nonneg_left ht2 (by positivity : (0:ℝ) ≤ c * ↑m)
      linarith
    have h2 : c * ↑m * (2 * (δ + 1)) ^ 2 =
      Real.log 2 * (4 * ↑m * (δ + 1) ^ 2) / (16 + 16 * ↑m * (δ + 1) ^ 2) := by
      simp only [c]; ring
    have h3 : Real.log 2 * (4 * ↑m * (δ + 1) ^ 2) / (16 + 16 * ↑m * (δ + 1) ^ 2)
      ≤ Real.log 2 := by
      rw [div_le_iff₀ hD_pos]
      nlinarith [hlog2_pos, sq_nonneg (δ + 1), hm_pos]
    linarith
  refine ⟨c, hc_pos, fun t ht => ?_⟩
  by_cases hcase : t ≥ 2 * (δ + 1)
  ·
    have hsub : {ω | |Y ω - center| ≥ t} ⊆ {ω | |Y ω - med| ≥ t / 2} := by
      intro ω hω
      simp only [mem_setOf_eq] at hω ⊢
      have h_tri : |Y ω - med| ≥ |Y ω - center| - δ := by
        have h := abs_sub_abs_le_abs_sub (Y ω - center) (Y ω - med)
        have h2 : (Y ω - center) - (Y ω - med) = med - center := by ring
        rw [h2] at h; linarith [abs_nonneg (med - center)]
      linarith
    have hmed_bound := hmed (t / 2) (by linarith)
    have hprob_mono : (μ {ω | |Y ω - center| ≥ t}).toReal ≤
      (μ {ω | |Y ω - med| ≥ t / 2}).toReal :=
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
    have hexp_mono : 2 * exp (-(↑m * (t / 2) ^ 2) / 4) ≤ 2 * exp (-c * ↑m * t ^ 2) := by
      have harg : -c * ↑m * t ^ 2 ≥ -(↑m * (t / 2) ^ 2) / 4 := by
        have h1 : -(↑m * (t / 2) ^ 2) / 4 = -(↑m * t ^ 2) / 16 := by ring
        rw [h1]
        have h2 : c * ↑m * t ^ 2 ≤ (1/16) * ↑m * t ^ 2 := by
          have := mul_le_mul_of_nonneg_right hc_le (by positivity : (0:ℝ) ≤ ↑m * t ^ 2)
          linarith
        linarith
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    linarith
  ·
    push_neg at hcase
    have hprob_le_1 : (μ {ω | |Y ω - center| ≥ t}).toReal ≤ 1 := by
      have h1 : (μ {ω | |Y ω - center| ≥ t}).toReal ≤ (μ Set.univ).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (subset_univ _))
      simp [measure_univ] at h1; exact h1
    have h2exp : (1 : ℝ) ≤ 2 * exp (-c * ↑m * t ^ 2) := by
      have hcmt : c * ↑m * t ^ 2 ≤ Real.log 2 := hsmall_bound t ht (by linarith)
      calc (1:ℝ) ≤ 2 * Real.exp (-(c * ↑m * t ^ 2)) := one_le_two_mul_exp_neg_aux hcmt
        _ = 2 * exp (-c * ↑m * t ^ 2) := by ring
    linarith

end RandomProjection

namespace RandomProjection

/--
[normProj_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/RandomProjection.lean)
-/
@[path]
lemma normProj_lipschitz
  {m d : ℕ}
  {x y : EuclideanSpace ℝ (Fin m)}
-- given
  (hd : d ≤ m) :
-- imply
  |normProj m d hd x - normProj m d hd y| ≤ ‖x - y‖ := by
-- proof
  unfold normProj
  let px : EuclideanSpace ℝ (Fin d) := (EuclideanSpace.equiv (Fin d) ℝ).symm
    (fun i => x (Fin.castLE hd i))
  let py : EuclideanSpace ℝ (Fin d) := (EuclideanSpace.equiv (Fin d) ℝ).symm
    (fun i => y (Fin.castLE hd i))
  have hpx_norm : ‖px‖ = Real.sqrt (∑ i : Fin d, (x (Fin.castLE hd i)) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have : px i = x (Fin.castLE hd i) := by simp [px]
    rw [this, Real.norm_eq_abs, sq_abs]
  have hpy_norm : ‖py‖ = Real.sqrt (∑ i : Fin d, (y (Fin.castLE hd i)) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have : py i = y (Fin.castLE hd i) := by simp [py]
    rw [this, Real.norm_eq_abs, sq_abs]
  rw [← hpx_norm, ← hpy_norm]
  calc |‖px‖ - ‖py‖| ≤ ‖px - py‖ := abs_norm_sub_norm_le px py
    _ ≤ ‖x - y‖ := by
      have h_pxpy_sq : ‖px - py‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
        have hinj : Function.Injective (Fin.castLE hd) := Fin.castLE_injective hd
        have h_coord : ∀ i : Fin d, (px - py) i = (x - y) (Fin.castLE hd i) := by
          intro i; simp [px, py]
        simp_rw [h_coord]
        calc ∑ i : Fin d, ((x - y) (Fin.castLE hd i)) ^ 2
          = ∑ j ∈ Finset.univ.map ⟨Fin.castLE hd, hinj⟩,
            ((x - y) j) ^ 2 := by
            rw [Finset.sum_map]; rfl
          _ ≤ ∑ j : Fin m, ((x - y) j) ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg _)
      nlinarith [norm_nonneg (px - py), norm_nonneg (x - y), h_pxpy_sq]

end RandomProjection

namespace RandomProjection

/--
[random_projection_concentration](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/RandomProjection.lean)
-/
@[path]
lemma random_projection_concentration
  {m d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {Z : Ω → EuclideanSpace ℝ (Fin m)}
-- given
  (hd : d ≤ m)
  (hm : 0 < m)
  (hLevy : ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ), (∀ x y : EuclideanSpace ℝ (Fin m), |f x - f y| ≤ ‖x - y‖) → ∃ med : ℝ, ∀ s : ℝ, s ≥ 0 → (μ {ω | |f (Z ω) - med| ≥ s}).toReal ≤ 2 * exp (-(↑m * s ^ 2) / 4)) :
-- imply
  ∃ c : ℝ, c > 0 ∧ ∀ t : ℝ, t ≥ 0 → (μ {ω | |normProj m d hd (Z ω) - Real.sqrt (↑d / ↑m)| ≥ t}).toReal ≤ 2 * exp (-c * ↑m * t ^ 2) := by
-- proof
  have hYLip : ∀ x y : EuclideanSpace ℝ (Fin m),
    |normProj m d hd x - normProj m d hd y| ≤ ‖x - y‖ :=
    fun x y => normProj_lipschitz hd x y
  obtain ⟨med, hmed⟩ := hLevy (normProj m d hd) hYLip
  exact tail_recenter_toReal hm hmed
end RandomProjection
namespace NearlyEquidistantPoints
open Real Set MeasureTheory
open scoped ENNReal NNReal
set_option maxHeartbeats 3200000


namespace NearlyEquidistantPoints

/--
[exp_two_log_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/RandomProjection.lean)
-/
@[path]
lemma exp_two_log_two
-- imply
  Real.exp (2 * Real.log 2) = 4 := by
-- proof
  have h1 : (2 : ℝ) * Real.log 2 = Real.log 2 + Real.log 2 := by ring
  rw [h1, exp_add, Real.exp_log (by positivity : (2:ℝ) > 0)]; norm_num

end NearlyEquidistantPoints

namespace NearlyEquidistantPoints

/--
[exp_half_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/RandomProjection.lean)
-/
@[path]
lemma exp_half_ge
  {e : ℝ}
-- given
  (he : e ≥ 2 * Real.log 2) :
-- imply
  Real.exp e / 2 ≥ Real.exp (e / 2) := by
-- proof
  have h1 : Real.exp (e / 2) ≥ 2 := by
    calc Real.exp (e / 2) ≥ Real.exp (Real.log 2) := exp_le_exp.mpr (by linarith)
      _ = 2 := Real.exp_log (by positivity)
  have h2 : Real.exp e = Real.exp (e / 2) * Real.exp (e / 2) := by
    rw [← exp_add]; ring_nf
  nlinarith

end NearlyEquidistantPoints

namespace NearlyEquidistantPoints

/--
[floor_exp_ge_two_of_log2_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/RandomProjection.lean)
-/
@[path]
lemma floor_exp_ge_two_of_log2_le
  {e : ℝ}
-- given
  (he : Real.log 2 ≤ e) :
-- imply
  2 ≤ ⌊Real.exp e⌋₊ := by
-- proof
  apply Nat.le_floor
  calc (↑2 : ℝ) = Real.exp (Real.log 2) := by
    rw [Real.exp_log (by positivity : (2:ℝ) > 0)]
    _ ≤ Real.exp e := exp_le_exp.mpr he

end NearlyEquidistantPoints

namespace NearlyEquidistantPoints

/--
[nearly_equidistant_points](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/RandomProjection.lean)
-/
@[path]
lemma nearly_equidistant_points
-- given
  (hJL : ∃ C : ℝ, C > 0 ∧ ∀ (ε : ℝ) (_hε : 0 < ε) (m N : ℕ) (d : ℕ) (X : Fin N → EuclideanSpace ℝ (Fin m)) (_hd : (d : ℝ) > C * ε⁻¹ ^ 2 * Real.log N), ∃ f : Fin N → EuclideanSpace ℝ (Fin d), ∀ i j : Fin N, i ≠ j → (1 - ε) * dist (X i) (X j) ≤ dist (f i) (f j) ∧ dist (f i) (f j) ≤ (1 + ε) * dist (X i) (X j))
  (hSimplex : ∀ (N : ℕ) (_hN : 2 ≤ N), ∃ X : Fin N → EuclideanSpace ℝ (Fin (N - 1)), ∀ i j : Fin N, i ≠ j → dist (X i) (X j) = 1) :
-- imply
  ∃ c : ℝ, c > 0 ∧ ∀ (ε : ℝ) (_hε : 0 < ε) (d : ℕ) (_hd : 0 < d), ∃ (N : ℕ) (S : Fin N → EuclideanSpace ℝ (Fin d)), (N : ℝ) ≥ Real.exp (c * ε ^ 2 * d) ∧ ∀ i j : Fin N, i ≠ j → 1 - ε ≤ dist (S i) (S j) ∧ dist (S i) (S j) ≤ 1 + ε := by
-- proof
  obtain ⟨C, hC_pos, hJL_use⟩ := hJL
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  intro ε hε d hd
  set e := ε ^ 2 * ↑d / (2 * C) with he_def
  have he_pos : 0 < e := by positivity
  have he_eq : e / 2 = 1 / (4 * C) * ε ^ 2 * ↑d := by simp only [he_def]; ring
  by_cases h_case : e ≥ 2 * Real.log 2
  ·
    set N := ⌊Real.exp e⌋₊
    have h_log2_le_e : Real.log 2 ≤ e := by
      linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]
    have hN_ge_2 : 2 ≤ N := floor_exp_ge_two_of_log2_le h_log2_le_e
    obtain ⟨X, hX_dist⟩ := hSimplex N hN_ge_2
    have hN_pos : (0 : ℝ) < (N : ℝ) :=
      Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hN_ge_2)
    have h_log_N : Real.log (↑N : ℝ) ≤ e :=
      (Real.log_le_log hN_pos (Nat.floor_le (le_of_lt (exp_pos e)))).trans_eq (Real.log_exp e)
    have h_JL_cond : (d : ℝ) > C * ε⁻¹ ^ 2 * Real.log ↑N := by
      have h_bound : C * ε⁻¹ ^ 2 * Real.log ↑N ≤ C * ε⁻¹ ^ 2 * e :=
        mul_le_mul_of_nonneg_left h_log_N (by positivity)
      have h_eq' : C * ε⁻¹ ^ 2 * e = (d : ℝ) / 2 := by
        simp only [he_def, inv_pow]; field_simp
      have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      linarith
    obtain ⟨f, hf⟩ := hJL_use ε hε (N - 1) N d X h_JL_cond
    refine ⟨N, f, ?_, ?_⟩
    ·
      rw [← he_eq]
      have h_floor_gt : (N : ℝ) > Real.exp e - 1 := Nat.sub_one_lt_floor (Real.exp e)
      have h_exp_ge_4 : Real.exp e ≥ 4 := by
        have h := exp_le_exp.mpr h_case; linarith [exp_two_log_two]
      linarith [exp_half_ge e h_case]
    ·
      intro i j hij
      have h := hf i j hij
      simp only [hX_dist i j hij, mul_one] at h
      exact h
  ·
    simp only [not_le] at h_case
    have h_exp_lt_2 : Real.exp (1 / (4 * C) * ε ^ 2 * ↑d) < 2 := by
      rw [← he_eq]
      calc Real.exp (e / 2) < Real.exp (Real.log 2) :=
        Real.exp_strictMono (by linarith)
        _ = 2 := Real.exp_log (by positivity)
    refine ⟨2, fun i => if (i : Fin 2) = 0 then (0 : EuclideanSpace ℝ (Fin d))
      else EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1, ?_, ?_⟩
    ·
      exact le_of_lt h_exp_lt_2
    ·
      intro i j hij
      have h_dist : dist
        (if (i : Fin 2) = 0 then (0 : EuclideanSpace ℝ (Fin d))
          else EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1)
        (if (j : Fin 2) = 0 then (0 : EuclideanSpace ℝ (Fin d))
          else EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1) = 1 := by
        fin_cases i <;> fin_cases j <;> simp_all [dist_comm, dist_eq_norm]
      rw [h_dist]
      exact ⟨by linarith, by linarith⟩

end NearlyEquidistantPoints


-- created on 2026-10-23
