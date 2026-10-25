import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Def_2_12
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter2.Def_2_12
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_6
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_19
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter2.Thm_2_14_SubspaceBound
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_6
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_19
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_14_SubspaceBound
open Matrix Finset BigOperators Rigollet MeasureTheory


/--
[thm_2_14_bic_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14.lean)
-/
@[path]
lemma thm_2_14_bic_bound
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {Y : Fin n → ℝ}
  {θstar : Fin d → ℝ}
  {eps : Fin n → ℝ}
  {τ : ℝ}
  {θhat : Fin d → ℝ}
  {t : ℝ}
-- given
  (hn : 0 < n)
  (hY : Y = X.mulVec θstar + eps)
  (_hτ : 0 < τ)
  (hBIC : IsBICEstimatorL2 X Y τ θhat)
  (ht : 0 ≤ t)
  (hnoise : ∀ (θ : Fin d → ℝ), 4 * (dotProduct eps (X.mulVec (θ - θstar))) ^ 2 ≤ dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) * (2 * ↑n * τ ^ 2 * (l0norm θ : ℝ) + t)) :
-- imply
  dotProduct (X.mulVec (θhat - θstar)) (X.mulVec (θhat - θstar)) ≤ 2 * ↑n * τ ^ 2 * (l0norm θstar : ℝ) + t := by
-- proof
  have h1 := hBIC.2 θstar
  subst hY
  have hres : (X.mulVec θstar + eps) - X.mulVec θhat = eps - X.mulVec (θhat - θstar) := by
    ext i; simp [Pi.sub_apply, Pi.add_apply, Matrix.mulVec_sub]; ring
  have hres_star : (X.mulVec θstar + eps) - X.mulVec θstar = eps := by
    ext i; simp [Pi.sub_apply, Pi.add_apply]
  rw [hres, hres_star] at h1
  set δ := X.mulVec (θhat - θstar) with hδ_def
  have hexpand : sqL2norm (eps - δ) = sqL2norm eps - 2 * ∑ i, eps i * δ i + sqL2norm δ := by
    simp only [sqL2norm, Pi.sub_apply]
    simp_rw [fun i : Fin n =>
      show (eps i - δ i) ^ 2 = eps i ^ 2 - 2 * (eps i * δ i) + δ i ^ 2 from by ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexpand] at h1
  have hD_eq : dotProduct δ δ = sqL2norm δ := by
    simp [sqL2norm, dotProduct]; congr 1; ext i; ring
  have hB_eq : dotProduct eps δ = ∑ i, eps i * δ i := by simp [dotProduct]
  set D := dotProduct δ δ with hD_def
  set B := dotProduct eps δ with hB_def2
  set a := ↑n * τ ^ 2 * (l0norm θhat : ℝ) with ha_def
  set b := ↑n * τ ^ 2 * (l0norm θstar : ℝ) with hb_def
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hD_nn : 0 ≤ D := by
    simp only [D, dotProduct]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (a := δ i))
  have hb_nn : 0 ≤ b := by
    simp only [hb_def]
    apply mul_nonneg (mul_nonneg (Nat.cast_nonneg' n) (sq_nonneg τ)) (Nat.cast_nonneg' (l0norm θstar))
  have hBIC_r : D ≤ 2 * B + b - a := by
    rw [hD_eq, hB_eq]
    show sqL2norm δ ≤ 2 * (∑ i, eps i * δ i) + b - a
    have key : 1 / ↑n * sqL2norm δ ≤ 1 / ↑n * (2 * (∑ i, eps i * δ i)) +
      (τ ^ 2 * (l0norm θstar : ℝ) - τ ^ 2 * (l0norm θhat : ℝ)) := by
      nlinarith [show 1 / (↑n : ℝ) * (sqL2norm eps - 2 * (∑ i, eps i * δ i) + sqL2norm δ) =
        1 / ↑n * sqL2norm eps - 1 / ↑n * (2 * (∑ i, eps i * δ i)) + 1 / ↑n * sqL2norm δ
          from by ring]
    have h2 : sqL2norm δ ≤ ↑n * (1 / ↑n * (2 * (∑ i, eps i * δ i)) +
      (τ ^ 2 * (l0norm θstar : ℝ) - τ ^ 2 * (l0norm θhat : ℝ))) := by
      calc sqL2norm δ = ↑n * (1 / ↑n * sqL2norm δ) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left key (le_of_lt hn_pos)
    have h3 : ↑n * (1 / ↑n * (2 * (∑ i, eps i * δ i)) +
      (τ ^ 2 * ↑(l0norm θstar) - τ ^ 2 * ↑(l0norm θhat))) =
      2 * (∑ i, eps i * δ i) + b - a := by
      simp only [ha_def, hb_def]; field_simp; ring
    linarith
  have hnoise' : 4 * B ^ 2 ≤ D * (2 * a + t) := by
    have := hnoise θhat
    rw [show dotProduct eps (X.mulVec (θhat - θstar)) = B from rfl,
      show dotProduct (X.mulVec (θhat - θstar)) (X.mulVec (θhat - θstar)) = D from rfl] at this
    convert this using 1
    simp only [ha_def]; ring
  suffices h : D ≤ 2 * b + t by
    have : 2 * b + t = 2 * ↑n * τ ^ 2 * ↑(l0norm θstar) + t := by
      simp only [hb_def]; ring
    linarith
  nlinarith [sq_nonneg (D - 2 * B)]

/--
[single_support_thm119_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14.lean)
-/
@[path]
lemma single_support_thm119_bound
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {σ : ℝ}
  {τsq : ℝ}
  {t : ℝ}
  {S : Finset (Fin d)}
  {k : ℕ}
-- given
  (hn : 0 < n)
  (hd : 0 < d)
  (hσ : 0 < σ)
  (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
  (hε_indep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
  (hε_meas : ∀ i : Fin n, Measurable (fun ω => ε ω i))
  (hτsq : 0 < τsq)
  (ht : 0 < t)
  (hSk : S.card = k)
  (hk1 : 1 ≤ k) :
-- imply
  μ {ω : Ω | ∃ (θ : Fin d → ℝ), (∀ j : Fin d, j ∉ S → θ j = 0) ∧ 4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 > dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) * (2 * ↑n * τsq * (l0norm θ : ℝ) + t)} ≤ ENNReal.ofReal ((6 : ℝ) ^ (k + l0norm θstar) * Real.exp (-t / (32 * σ ^ 2) - ↑n * τsq * ↑k / (16 * σ ^ 2))) :=
-- proof
  single_support_thm119_bound' hn hd X θstar ε σ hσ hε hε_indep hε_meas τsq hτsq t ht S k hSk hk1

/--
[per_size_thm119_raw_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14.lean)
-/
@[path]
lemma per_size_thm119_raw_bound
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {σ : ℝ}
  {τsq : ℝ}
  {t : ℝ}
  {k : ℕ}
-- given
  (hn : 0 < n)
  (hd : 0 < d)
  (hσ : 0 < σ)
  (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
  (hε_indep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
  (hε_meas : ∀ i : Fin n, Measurable (fun ω => ε ω i))
  (hτsq : 0 < τsq)
  (ht : 0 < t)
  (hk : k ∈ Finset.Icc 1 d) :
-- imply
  μ {ω : Ω | ∃ (θ : Fin d → ℝ), l0norm θ ≤ k ∧ 4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 > dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) * (2 * ↑n * τsq * (l0norm θ : ℝ) + t)} ≤ ENNReal.ofReal (↑(Nat.choose d k) * (6 : ℝ) ^ (k + l0norm θstar) * Real.exp (-t / (32 * σ ^ 2) - ↑n * τsq * ↑k / (16 * σ ^ 2))) := by
-- proof
  rw [Finset.mem_Icc] at hk
  obtain ⟨hk1, hkd⟩ := hk
  set badS := fun (S : Finset (Fin d)) => {ω : Ω | ∃ (θ : Fin d → ℝ),
    (∀ j : Fin d, j ∉ S → θ j = 0) ∧
    4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 >
      dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) *
      (2 * ↑n * τsq * (l0norm θ : ℝ) + t)} with hbadS_def
  set C := (6 : ℝ) ^ (k + l0norm θstar) *
    Real.exp (-t / (32 * σ ^ 2) - ↑n * τsq * ↑k / (16 * σ ^ 2)) with hC_def
  have hcontain : {ω : Ω | ∃ (θ : Fin d → ℝ), l0norm θ ≤ k ∧
    4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 >
      dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) *
      (2 * ↑n * τsq * (l0norm θ : ℝ) + t)} ⊆
    ⋃ S ∈ (Finset.univ : Finset (Fin d)).powersetCard k, badS S := by
    intro ω ⟨θ, hl0, hbad⟩
    simp only [Set.mem_iUnion]
    have hsupp_le : (Finset.univ.filter (fun j => θ j ≠ 0)).card ≤ k := by
      rw [l0norm_eq] at hl0; exact hl0
    obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_superset_card_eq hsupp_le
      (by rwa [Fintype.card_fin])
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hS_card⟩, ?_⟩
    exact ⟨θ, fun j hj => by
      by_contra h
      exact hj (hS_sub (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)), hbad⟩
  have hunion : μ (⋃ S ∈ (Finset.univ : Finset (Fin d)).powersetCard k, badS S) ≤
    ∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard k, μ (badS S) :=
    measure_biUnion_finset_le _ _
  have hper_S : ∀ S ∈ (Finset.univ : Finset (Fin d)).powersetCard k,
    μ (badS S) ≤ ENNReal.ofReal C := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    exact single_support_thm119_bound hn hd X θstar ε σ hσ hε hε_indep hε_meas τsq hτsq t ht S k hS.2 hk1
  have hsum : ∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard k, μ (badS S) ≤
    ((Finset.univ : Finset (Fin d)).powersetCard k).card • ENNReal.ofReal C :=
    Finset.sum_le_card_nsmul _ _ _ hper_S
  have hcard : ((Finset.univ : Finset (Fin d)).powersetCard k).card = Nat.choose d k := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hnsmul : (Nat.choose d k) • ENNReal.ofReal C =
    ENNReal.ofReal (↑(Nat.choose d k) * C) := by
    rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ENNReal.ofReal_mul (Nat.cast_nonneg' _)]
  calc μ _ ≤ μ (⋃ S ∈ (Finset.univ : Finset (Fin d)).powersetCard k, badS S) :=
    measure_mono hcontain
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard k, μ (badS S) := hunion
    _ ≤ ((Finset.univ : Finset (Fin d)).powersetCard k).card • ENNReal.ofReal C := hsum
    _ = (Nat.choose d k) • ENNReal.ofReal C := by rw [hcard]
    _ = ENNReal.ofReal (↑(Nat.choose d k) * C) := hnsmul
    _ = ENNReal.ofReal (↑(Nat.choose d k) * (6 : ℝ) ^ (k + l0norm θstar) *
      Real.exp (-t / (32 * σ ^ 2) - ↑n * τsq * ↑k / (16 * σ ^ 2))) := by
      congr 1; rw [hC_def]; ring

/--
[per_size_concentration_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14.lean)
-/
@[path]
lemma per_size_concentration_bound
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {σ : ℝ}
  {τsq : ℝ}
  {t : ℝ}
  {k : ℕ}
-- given
  (hn : 0 < n)
  (hd : 0 < d)
  (hσ : 0 < σ)
  (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
  (hε_indep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
  (hε_meas : ∀ i : Fin n, Measurable (fun ω => ε ω i))
  (hτsq : τsq ≥ (16 * Real.log 6 + 32 * Real.log (Real.exp 1 * ↑d)) * σ ^ 2 / ↑n)
  (ht : 0 < t)
  (hk : k ∈ Finset.Icc 1 d) :
-- imply
  μ {ω : Ω | ∃ (θ : Fin d → ℝ), l0norm θ ≤ k ∧ 4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 > dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) * (2 * ↑n * τsq * (l0norm θ : ℝ) + t)} ≤ ENNReal.ofReal (Real.exp (-t / (32 * σ ^ 2) - ↑k * Real.log (Real.exp 1 * ↑d) + ↑(l0norm θstar) * Real.log 12)) := by
-- proof
  rw [Finset.mem_Icc] at hk
  obtain ⟨hk1, hkd⟩ := hk
  set ed := Real.exp 1 * (↑d : ℝ) with hed_def
  set s₀ := l0norm θstar with hs₀_def
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hd_pos : (0 : ℝ) < ↑d := Nat.cast_pos.mpr hd
  have hed_pos : (0 : ℝ) < ed := mul_pos (Real.exp_pos 1) hd_pos
  have hσ2_pos : (0 : ℝ) < σ ^ 2 := sq_pos_of_pos hσ
  have hlog6_pos : (0 : ℝ) < Real.log 6 := Real.log_pos (by norm_num)
  have hloged_pos : (0 : ℝ) < Real.log ed := by
    apply Real.log_pos
    calc (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ ≤ Real.exp 1 * ↑d := le_mul_of_one_le_right (Real.exp_pos 1).le
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd))
  have hτsq_pos : 0 < τsq := by
    calc (0 : ℝ) < (16 * Real.log 6 + 32 * Real.log ed) * σ ^ 2 / ↑n :=
      div_pos (mul_pos (by linarith) hσ2_pos) hn_pos
      _ ≤ τsq := hτsq
  have hraw := per_size_thm119_raw_bound hn hd X θstar ε σ hσ hε hε_indep hε_meas τsq hτsq_pos t ht k
    (Finset.mem_Icc.mpr ⟨hk1, hkd⟩)
  calc μ _ ≤ ENNReal.ofReal (↑(Nat.choose d k) * (6 : ℝ) ^ (k + s₀) *
    Real.exp (-t / (32 * σ ^ 2) - ↑n * τsq * ↑k / (16 * σ ^ 2))) := hraw
    _ ≤ ENNReal.ofReal (Real.exp (-t / (32 * σ ^ 2) - ↑k * Real.log ed +
      ↑s₀ * Real.log 12)) := by
      apply ENNReal.ofReal_le_ofReal
      have hchoose_le : (↑(Nat.choose d k) : ℝ) ≤ ed ^ k := by
        calc (↑(Nat.choose d k) : ℝ) ≤ (Real.exp 1 * ↑d / ↑k) ^ k := by
          exact_mod_cast lemma_2_7 d k hk1 hkd
          _ ≤ ed ^ k := by
            apply pow_le_pow_left₀ (by positivity)
            exact div_le_self (by positivity) (by exact_mod_cast hk1)
      have h6split : (6 : ℝ) ^ (k + s₀) = (6 : ℝ) ^ k * (6 : ℝ) ^ s₀ := pow_add 6 k s₀
      have hprod_le : (↑(Nat.choose d k) : ℝ) * (6 : ℝ) ^ k ≤ (6 * ed) ^ k := by
        calc (↑(Nat.choose d k) : ℝ) * 6 ^ k ≤ ed ^ k * 6 ^ k :=
          mul_le_mul_of_nonneg_right hchoose_le (pow_nonneg (by norm_num) k)
          _ = (ed * 6) ^ k := (mul_pow ed 6 k).symm
          _ = (6 * ed) ^ k := by ring_nf
      have h6ed_exp : (6 * ed) ^ k = Real.exp (↑k * Real.log (6 * ed)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by positivity : 0 < 6 * ed)]
      have h6s_exp : (6 : ℝ) ^ s₀ = Real.exp (↑s₀ * Real.log 6) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 6)]
      have hlog_6ed : Real.log (6 * ed) = Real.log 6 + Real.log ed := by
        rw [Real.log_mul (by norm_num : (6:ℝ) ≠ 0) (ne_of_gt hed_pos)]
      have hτ_bound : ↑n * τsq / (16 * σ ^ 2) ≥ Real.log 6 + 2 * Real.log ed := by
        rw [ge_iff_le]
        have h_mul : (16 * Real.log 6 + 32 * Real.log ed) * σ ^ 2 ≤ ↑n * τsq := by
          rw [ge_iff_le, div_le_iff₀ hn_pos] at hτsq; linarith
        have h_div : (16 * Real.log 6 + 32 * Real.log ed) * σ ^ 2 / (16 * σ ^ 2) ≤
          ↑n * τsq / (16 * σ ^ 2) :=
          div_le_div_of_nonneg_right h_mul (by positivity)
        have h_simp : (16 * Real.log 6 + 32 * Real.log ed) * σ ^ 2 / (16 * σ ^ 2) =
          Real.log 6 + 2 * Real.log ed := by
          rw [mul_div_mul_right _ _ (ne_of_gt hσ2_pos)]; ring
        linarith
      have hexp_ineq : ↑k * Real.log (6 * ed) + ↑s₀ * Real.log 6 +
        (-t / (32 * σ ^ 2) - ↑n * τsq * ↑k / (16 * σ ^ 2)) ≤
        -t / (32 * σ ^ 2) - ↑k * Real.log ed + ↑s₀ * Real.log 12 := by
        rw [hlog_6ed]
        have hk_pos : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (by omega)
        have hlog6_le_log12 : Real.log 6 ≤ Real.log 12 :=
          Real.log_le_log (by norm_num) (by norm_num)
        have h1 : ↑n * τsq * ↑k / (16 * σ ^ 2) = ↑k * (↑n * τsq / (16 * σ ^ 2)) := by ring
        rw [h1]
        have hs₀_nn : (0 : ℝ) ≤ (↑s₀ : ℝ) := Nat.cast_nonneg' s₀
        nlinarith
      calc (↑(Nat.choose d k) : ℝ) * (6 : ℝ) ^ (k + s₀) *
        Real.exp (-t / (32 * σ ^ 2) - ↑n * τsq * ↑k / (16 * σ ^ 2))
        = ↑(Nat.choose d k) * 6 ^ k * 6 ^ s₀ *
          Real.exp (-t / (32 * σ ^ 2) - ↑n * τsq * ↑k / (16 * σ ^ 2)) := by
          rw [h6split]; ring
        _ ≤ (6 * ed) ^ k * 6 ^ s₀ *
          Real.exp (-t / (32 * σ ^ 2) - ↑n * τsq * ↑k / (16 * σ ^ 2)) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right hprod_le (pow_nonneg (by norm_num) s₀)
          · exact (Real.exp_pos _).le
        _ = Real.exp (↑k * Real.log (6 * ed) + ↑s₀ * Real.log 6 +
          (-t / (32 * σ ^ 2) - ↑n * τsq * ↑k / (16 * σ ^ 2))) := by
          rw [h6ed_exp, h6s_exp]
          rw [← Real.exp_add, ← Real.exp_add]
        _ ≤ Real.exp (-t / (32 * σ ^ 2) - ↑k * Real.log ed + ↑s₀ * Real.log 12) :=
          Real.exp_le_exp_of_le hexp_ineq

/--
[sup_out_intermediate_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14.lean)
-/
@[path]
lemma sup_out_intermediate_bound
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {σ : ℝ}
  {τsq : ℝ}
  {t : ℝ}
-- given
  (hn : 0 < n)
  (hd : 0 < d)
  (hσ : 0 < σ)
  (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
  (hε_indep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
  (hε_meas : ∀ i : Fin n, Measurable (fun ω => ε ω i))
  (hτsq : τsq ≥ (16 * Real.log 6 + 32 * Real.log (Real.exp 1 * ↑d)) * σ ^ 2 / ↑n)
  (ht : 0 < t) :
-- imply
  μ {ω : Ω | ∃ (θ : Fin d → ℝ), 4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 > dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) * (2 * ↑n * τsq * (l0norm θ : ℝ) + t)} ≤ ∑ k ∈ Finset.Icc 1 d, ENNReal.ofReal (Real.exp (-t / (32 * σ ^ 2) - ↑k * Real.log (Real.exp 1 * ↑d) + ↑(l0norm θstar) * Real.log 12)) := by
-- proof
  set S := fun k => {ω : Ω | ∃ (θ : Fin d → ℝ), l0norm θ ≤ k ∧
    4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 >
      dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) *
      (2 * ↑n * τsq * (l0norm θ : ℝ) + t)} with hS_def
  have hcontain : {ω : Ω | ∃ (θ : Fin d → ℝ),
    4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 >
      dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) *
      (2 * ↑n * τsq * (l0norm θ : ℝ) + t)} ⊆
    ⋃ k ∈ Finset.Icc 1 d, S k := by
    intro ω ⟨θ, hbad⟩
    simp only [Set.mem_iUnion]
    by_cases hθ : θ = 0
    ·
      subst hθ
      exact ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hd⟩,
        Set.mem_setOf.mpr ⟨0, by rw [l0norm_zero]; exact Nat.zero_le 1, hbad⟩⟩
    ·
      have hl0_pos : l0norm θ ≠ 0 := by
        rw [l0norm_eq]
        rw [Finset.card_ne_zero, Finset.filter_nonempty_iff]
        by_contra h
        push Not at h
        exact hθ (funext fun j => by simpa using h j (Finset.mem_univ j))
      have hl0_le : l0norm θ ≤ d := by
        rw [l0norm_eq]
        calc (Finset.univ.filter fun j => θ j ≠ 0).card
          ≤ Finset.univ.card := Finset.card_filter_le _ _
          _ = d := Finset.card_fin d
      exact ⟨l0norm θ, Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hl0_pos, hl0_le⟩,
        θ, le_refl _, hbad⟩
  calc μ _ ≤ μ (⋃ k ∈ Finset.Icc 1 d, S k) := MeasureTheory.measure_mono hcontain
    _ ≤ ∑ k ∈ Finset.Icc 1 d, μ (S k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 d, ENNReal.ofReal
      (Real.exp (-t / (32 * σ ^ 2) - ↑k * Real.log (Real.exp 1 * ↑d) +
        ↑(l0norm θstar) * Real.log 12)) := by
      apply Finset.sum_le_sum
      intro k hk
      have := per_size_concentration_bound hn hd X θstar ε σ hσ hε hε_indep hε_meas τsq hτsq t ht k hk
      exact this

/--
[sup_out_probability_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14.lean)
-/
@[path]
lemma sup_out_probability_bound
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {σ : ℝ}
  {τsq : ℝ}
  {t : ℝ}
-- given
  (hn : 0 < n)
  (hd : 0 < d)
  (hσ : 0 < σ)
  (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
  (hε_indep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
  (hε_meas : ∀ i : Fin n, Measurable (fun ω => ε ω i))
  (hτsq : τsq ≥ (16 * Real.log 6 + 32 * Real.log (Real.exp 1 * ↑d)) * σ ^ 2 / ↑n)
  (ht : 0 < t) :
-- imply
  μ {ω : Ω | ∃ (θ : Fin d → ℝ), 4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 > dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) * (2 * ↑n * τsq * (l0norm θ : ℝ) + t)} ≤ ENNReal.ofReal (Real.exp (-t / (32 * σ ^ 2) + ↑(l0norm θstar) * Real.log 12)) := by
-- proof
  have h_inter := sup_out_intermediate_bound hn hd X θstar ε σ hσ hε hε_indep hε_meas τsq hτsq t ht
  calc μ _ ≤ ∑ k ∈ Finset.Icc 1 d, ENNReal.ofReal (Real.exp
    (-t / (32 * σ ^ 2) - ↑k * Real.log (Real.exp 1 * ↑d) +
      ↑(l0norm θstar) * Real.log 12)) := h_inter
    _ ≤ ENNReal.ofReal (Real.exp (-t / (32 * σ ^ 2) + ↑(l0norm θstar) * Real.log 12)) := by
      set C := Real.exp (-t / (32 * σ ^ 2) + ↑(l0norm θstar) * Real.log 12) with hC_def
      have hed_gt_one : (1 : ℝ) < Real.exp 1 * ↑d := by
        calc (1 : ℝ) < Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ); linarith
          _ = Real.exp 1 * 1 := (mul_one _).symm
          _ ≤ Real.exp 1 * ↑d := by
            apply mul_le_mul_of_nonneg_left
            · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd)
            · exact le_of_lt (Real.exp_pos 1)
      have hed_pos : (0 : ℝ) < Real.exp 1 * ↑d := by linarith
      have hfactor : ∀ k ∈ Finset.Icc 1 d,
        ENNReal.ofReal (Real.exp (-t / (32 * σ ^ 2) - ↑k * Real.log (Real.exp 1 * ↑d) +
          ↑(l0norm θstar) * Real.log 12)) =
        ENNReal.ofReal (C * (1 / (Real.exp 1 * ↑d)) ^ k) := by
        intro k _
        congr 1
        rw [hC_def]
        rw [show -t / (32 * σ ^ 2) - ↑k * Real.log (Real.exp 1 * ↑d) +
          ↑(l0norm θstar) * Real.log 12 =
          (-t / (32 * σ ^ 2) + ↑(l0norm θstar) * Real.log 12) +
          (-(↑k * Real.log (Real.exp 1 * ↑d))) from by ring]
        rw [Real.exp_add]
        rw [show (-(↑k * Real.log (Real.exp 1 * ↑d)) : ℝ) =
          ↑k * (-Real.log (Real.exp 1 * ↑d)) from by ring]
        rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hed_pos, inv_eq_one_div]
      rw [Finset.sum_congr rfl hfactor]
      set r := 1 / (Real.exp 1 * ↑d) with hr_def
      have hr_pos : 0 < r := by positivity
      have hr_lt_one : r < 1 := by
        rw [hr_def, div_lt_one hed_pos]; exact hed_gt_one
      have hC_pos : 0 < C := Real.exp_pos _
      rw [show (∑ k ∈ Finset.Icc 1 d, ENNReal.ofReal (C * r ^ k)) =
        ENNReal.ofReal (∑ k ∈ Finset.Icc 1 d, C * r ^ k) from by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro k _; exact mul_nonneg hC_pos.le (pow_nonneg hr_pos.le k)]
      apply ENNReal.ofReal_le_ofReal
      rw [← _root_.Finset.mul_sum]
      suffices hsub : ∑ k ∈ Finset.Icc 1 d, r ^ k ≤ 1 by
        linarith [mul_le_mul_of_nonneg_left hsub hC_pos.le]
      calc ∑ k ∈ Finset.Icc 1 d, r ^ k
        ≤ ∑ _k ∈ Finset.Icc 1 d, r := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_Icc] at hk
          have := pow_le_pow_of_le_one hr_pos.le hr_lt_one.le hk.1
          simpa [pow_one] using this
        _ = ↑d * r := by
          rw [Finset.sum_const, nsmul_eq_mul]
          congr 1
          have : (Finset.Icc 1 d).card = d := by rw [Nat.card_Icc]; omega
          exact_mod_cast this
        _ ≤ 1 := by
          rw [hr_def]
          have hd_pos : (0 : ℝ) < ↑d := Nat.cast_pos.mpr hd
          rw [show (↑d : ℝ) * (1 / (Real.exp 1 * ↑d)) = 1 / Real.exp 1 from by field_simp]
          rw [div_le_one (Real.exp_pos 1)]
          linarith [Real.add_one_le_exp (1 : ℝ)]

/--
[noise_concentration_bound_thm214](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14.lean)
-/
@[path]
lemma noise_concentration_bound_thm214
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {σ : ℝ}
  {δ : ℝ}
-- given
  (hn : 0 < n)
  (hd : 0 < d)
  (hσ : 0 < σ)
  (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
  (hε_indep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
  (hε_meas : ∀ i : Fin n, Measurable (fun ω => ε ω i))
  (hδ₀ : 0 < δ)
  (hδ₁ : δ < 1) :
-- imply
  μ {ω : Ω | ∀ (θ : Fin d → ℝ), 4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 ≤ dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) * (2 * ↑n * ((16 * Real.log 6 + 32 * Real.log (Real.exp 1 * ↑d)) * σ ^ 2 / ↑n) * (l0norm θ : ℝ) + (32 * σ ^ 2 * ↑(l0norm θstar) * Real.log 12 + 32 * σ ^ 2 * Real.log (1 / δ)))} ≥ ENNReal.ofReal (1 - δ) := by
-- proof
  set τsq := (16 * Real.log 6 + 32 * Real.log (Real.exp 1 * ↑d)) * σ ^ 2 / ↑n with hτsq_def
  set t := 32 * σ ^ 2 * ↑(l0norm θstar) * Real.log 12 + 32 * σ ^ 2 * Real.log (1 / δ)
    with ht_def
  have hlog12 : (0 : ℝ) < Real.log 12 := Real.log_pos (by norm_num)
  have hlog_inv_δ : (0 : ℝ) < Real.log (1 / δ) := by
    apply Real.log_pos; rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ₀, hδ₁⟩
  have hσ2_pos : (0 : ℝ) < σ ^ 2 := sq_pos_of_pos hσ
  have ht_pos : 0 < t := by
    simp only [ht_def]
    have h1 : 0 < 32 * σ ^ 2 * ↑(l0norm θstar) * Real.log 12 + 32 * σ ^ 2 * Real.log (1 / δ) := by
      have : 0 < 32 * σ ^ 2 * Real.log (1 / δ) := by positivity
      have : 0 ≤ 32 * σ ^ 2 * ↑(l0norm θstar) * Real.log 12 := by positivity
      linarith
    exact h1
  have hcompl : {ω : Ω | ∀ (θ : Fin d → ℝ),
    4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 ≤
      dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) *
      (2 * ↑n * τsq * (l0norm θ : ℝ) + t)}ᶜ =
    {ω : Ω | ∃ (θ : Fin d → ℝ),
      4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 >
        dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) *
        (2 * ↑n * τsq * (l0norm θ : ℝ) + t)} := by
    ext ω; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le]
  have h_supout := sup_out_probability_bound hn hd X θstar ε σ hσ hε hε_indep hε_meas τsq (le_refl τsq) t ht_pos
  have hσ2_ne : σ ^ 2 ≠ 0 := ne_of_gt hσ2_pos
  have h_exp_eq : Real.exp (-t / (32 * σ ^ 2) + ↑(l0norm θstar) * Real.log 12) = δ := by
    have h1 : -t / (32 * σ ^ 2) = -(↑(l0norm θstar) * Real.log 12 + Real.log (1 / δ)) := by
      simp only [ht_def]; field_simp
    rw [h1]
    have h2 : -(↑(l0norm θstar) * Real.log 12 + Real.log (1 / δ)) + ↑(l0norm θstar) * Real.log 12 = -Real.log (1 / δ) := by ring
    rw [h2]
    rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 1 / δ)]
    rw [one_div, inv_inv]
  have h_compl_le_δ : μ {ω : Ω | ∃ (θ : Fin d → ℝ),
    4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 >
      dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) *
      (2 * ↑n * τsq * (l0norm θ : ℝ) + t)} ≤ ENNReal.ofReal δ := by
    calc μ _ ≤ ENNReal.ofReal (Real.exp (-t / (32 * σ ^ 2) + ↑(l0norm θstar) * Real.log 12)) :=
      h_supout
      _ = ENNReal.ofReal δ := by rw [h_exp_eq]
  set E := {ω : Ω | ∀ (θ : Fin d → ℝ),
    4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 ≤
      dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) *
      (2 * ↑n * τsq * (l0norm θ : ℝ) + t)} with hE_def
  have hEc_eq : Eᶜ = {ω : Ω | ∃ (θ : Fin d → ℝ),
    4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 >
      dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) *
      (2 * ↑n * τsq * (l0norm θ : ℝ) + t)} := by
    ext ω; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le, hE_def]
  have hEc_le : μ Eᶜ ≤ ENNReal.ofReal δ := by rw [hEc_eq]; exact h_compl_le_δ
  have h1 : μ Set.univ ≤ μ E + μ Eᶜ := by
    rw [← Set.union_compl_self E]
    exact MeasureTheory.measure_union_le E Eᶜ
  rw [MeasureTheory.IsProbabilityMeasure.measure_univ] at h1
  have h3 : ENNReal.ofReal (1 - δ) = 1 - ENNReal.ofReal δ := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_sub 1 (le_of_lt hδ₀)
  rw [ge_iff_le, h3]
  calc 1 - ENNReal.ofReal δ
    ≤ 1 - μ Eᶜ := tsub_le_tsub_left hEc_le 1
    _ ≤ μ E := tsub_le_iff_right.mpr h1

/--
[thm_2_14_probabilistic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14.lean)
-/
@[path]
lemma thm_2_14_probabilistic
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {σ : ℝ}
  {δ : ℝ}
  {θhat : Ω → Fin d → ℝ}
-- given
  (hn : 0 < n)
  (hd : 0 < d)
  (hσ : 0 < σ)
  (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
  (hε_indep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
  (hε_meas : ∀ i : Fin n, Measurable (fun ω => ε ω i))
  (hδ₀ : 0 < δ)
  (hδ₁ : δ < 1)
  (hBIC : ∀ ω, IsBICEstimatorL2 X (X.mulVec θstar + ε ω) (Real.sqrt ((16 * Real.log 6 + 32 * Real.log (Real.exp 1 * ↑d)) * σ ^ 2 / ↑n)) (θhat ω)) :
-- imply
  μ {ω : Ω | dotProduct (X.mulVec (θhat ω - θstar)) (X.mulVec (θhat ω - θstar)) ≤ 224 * ↑(l0norm θstar) * σ ^ 2 * Real.log (Real.exp 1 * ↑d) + 32 * σ ^ 2 * Real.log (1 / δ)} ≥ ENNReal.ofReal (1 - δ) := by
-- proof
  have hconc := noise_concentration_bound_thm214 hn hd X θstar ε σ hσ hε hε_indep hε_meas δ hδ₀ hδ₁
  apply le_trans hconc
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  set τ := Real.sqrt ((16 * Real.log 6 + 32 * Real.log (Real.exp 1 * ↑d)) * σ ^ 2 / ↑n)
    with hτ_def
  set t := 32 * σ ^ 2 * ↑(l0norm θstar) * Real.log 12 + 32 * σ ^ 2 * Real.log (1 / δ)
    with ht_def
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hd_pos : (0 : ℝ) < ↑d := Nat.cast_pos.mpr hd
  have hlog6 : (0 : ℝ) < Real.log 6 := Real.log_pos (by norm_num)
  have hloged : (0 : ℝ) < Real.log (Real.exp 1 * ↑d) := by
    apply Real.log_pos
    calc (1 : ℝ) < Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
      _ = Real.exp 1 * 1 := (mul_one _).symm
      _ ≤ Real.exp 1 * ↑d := by
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd)
        · exact le_of_lt (Real.exp_pos 1)
  have hτ_sq_pos : 0 < (16 * Real.log 6 + 32 * Real.log (Real.exp 1 * ↑d)) * σ ^ 2 / ↑n := by
    apply div_pos
    · exact mul_pos (by linarith) (sq_pos_of_pos hσ)
    · exact hn_pos
  have hτ_pos : 0 < τ := Real.sqrt_pos_of_pos hτ_sq_pos
  have hlog12 : (0 : ℝ) < Real.log 12 := Real.log_pos (by norm_num)
  have hlog_inv_δ : (0 : ℝ) < Real.log (1 / δ) := by
    apply Real.log_pos; rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ₀, hδ₁⟩
  have ht_nn : 0 ≤ t := by
    simp only [ht_def]
    have h1 : 0 ≤ 32 * σ ^ 2 * ↑(l0norm θstar) * Real.log 12 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg σ)) (Nat.cast_nonneg' _)) hlog12.le
    have h2 : 0 ≤ 32 * σ ^ 2 * Real.log (1 / δ) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg σ)) hlog_inv_δ.le
    linarith
  have hτ_sq : τ ^ 2 = (16 * Real.log 6 + 32 * Real.log (Real.exp 1 * ↑d)) * σ ^ 2 / ↑n := by
    simp only [hτ_def]; exact Real.sq_sqrt (le_of_lt hτ_sq_pos)
  have hnoise : ∀ (θ : Fin d → ℝ),
    4 * (dotProduct (ε ω) (X.mulVec (θ - θstar))) ^ 2 ≤
      dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) *
      (2 * ↑n * τ ^ 2 * (l0norm θ : ℝ) + t) := by
    intro θ; have := hω θ; rw [hτ_sq]; exact this
  have hdet := thm_2_14_bic_bound hn X (X.mulVec θstar + ε ω) θstar (ε ω) rfl τ hτ_pos
    (θhat ω) (hBIC ω) t ht_nn hnoise
  apply le_trans hdet
  rw [hτ_sq]; simp only [ht_def]
  have hsimp : 2 * ↑n * ((16 * Real.log 6 + 32 * Real.log (Real.exp 1 * ↑d)) * σ ^ 2 / ↑n) *
    ↑(l0norm θstar) =
    (32 * Real.log 6 + 64 * Real.log (Real.exp 1 * ↑d)) * σ ^ 2 * ↑(l0norm θstar) := by
    field_simp; ring
  rw [hsimp]
  have hlog72 : Real.log 6 + Real.log 12 < 5 := by
    rw [← Real.log_mul (by norm_num : (6:ℝ) ≠ 0) (by norm_num : (12:ℝ) ≠ 0)]
    norm_num
    rw [show (5 : ℝ) = Real.log (Real.exp 5) from (Real.log_exp 5).symm]
    apply Real.log_lt_log (by norm_num : (0 : ℝ) < 72)
    have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 5 by norm_num) 6
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num at h; linarith
  have hloged_ge : 1 ≤ Real.log (Real.exp 1 * ↑d) := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (Real.exp 1 * ↑d) := by
        apply Real.log_le_log (Real.exp_pos 1)
        exact le_mul_of_one_le_right (Real.exp_pos 1).le
          (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd))
  have hσ2_nn : 0 ≤ σ ^ 2 := sq_nonneg σ
  have hl0_nn : (0 : ℝ) ≤ ↑(l0norm θstar) := Nat.cast_nonneg' _
  nlinarith [mul_nonneg hσ2_nn hl0_nn]


-- created on 2026-10-23
