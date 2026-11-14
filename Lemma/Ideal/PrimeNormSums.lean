import Mathlib
import Def.FrobeniusDensity_PrimeSums

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NumberField.PrimeNormSum

open NumberField NumberField.InfinitePlace IsDedekindDomain Filter Topology
open scoped Classical

section PrimeSums

variable (F : Type) [Field F] [NumberField F] {m : ℕ} [NeZero m]

def pw (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) : ℝ := (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)

variable {F}

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem one_lt_absNorm_real (v : HeightOneSpectrum (𝓞 F)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have := two_le_absNorm v
  exact_mod_cast (by omega : 1 < Ideal.absNorm v.asIdeal)

theorem pw_pos (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) : 0 < pw F s v :=
  Real.rpow_pos_of_pos (by linarith [one_lt_absNorm_real v]) _

theorem pw_nonneg (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) : 0 ≤ pw F s v := (pw_pos s v).le

theorem pw_le_one {s : ℝ} (hs : 0 ≤ s) (v : HeightOneSpectrum (𝓞 F)) : pw F s v ≤ 1 := by
  unfold pw
  exact Real.rpow_le_one_of_one_le_of_nonpos (one_lt_absNorm_real v).le (by linarith)

theorem pw_antitone {s s' : ℝ} (h : s ≤ s') (v : HeightOneSpectrum (𝓞 F)) : pw F s' v ≤ pw F s v := by
  unfold pw
  exact Real.rpow_le_rpow_of_exponent_le (one_lt_absNorm_real v).le (by linarith)

theorem tendsto_sum_card_div :
    Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / n) atTop
      (𝓝 ((2 ^ nrRealPlaces F * (2 * Real.pi) ^ nrComplexPlaces F * Units.regulator F *
        classNumber F) / (Units.torsionOrder F * Real.sqrt |discr F|))) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem summable_card_absNorm {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) s := by
  set d : ℕ → ℝ := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) with hd
  have h1 := (tendsto_sum_card_div (F := F)).isBigO_one ℝ
  have h2 : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, d k) =ᶠ[atTop]
      fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n, d k) / n * n := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, d k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine h2.trans_isBigO ?_
    have h3 := h1.mul (Asymptotics.isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop)
    refine h3.congr_right fun n ↦ ?_
    rw [Real.rpow_one, one_mul]
  have h4 := LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun n ↦ Nat.cast_nonneg _)
    zero_le_one (by simpa using hs)
  refine (LSeriesSummable_congr s fun {n} _ ↦ ?_).1 h4
  simp [hd]

theorem summable_dedekind_terms {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by
  have h4 := summable_card_absNorm (F := F) (s := (s : ℂ)) (by simpa using hs)
  have h5 := h4.norm
  refine (h5.congr fun n => ?_)
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · rw [if_pos hn, hn, Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [if_neg hn, Complex.norm_natCast, Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg _),
      div_eq_mul_inv]

theorem summable_pw {s : ℝ} (hs : 1 < s) : Summable (pw F s) := by
  set e : ℕ → ℝ := fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)
    with he
  have h5 : Summable e := summable_dedekind_terms hs

  refine summable_of_sum_le (fun v => pw_nonneg s v) (c := ∑' n, e n) fun T => ?_
  have hmaps : ∀ v ∈ T, Ideal.absNorm v.asIdeal ∈ T.image fun v => Ideal.absNorm v.asIdeal :=
    fun v hv => Finset.mem_image_of_mem _ hv
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hstep : ∀ n : ℕ, ∀ S : Finset (HeightOneSpectrum (𝓞 F)),
      (∀ v ∈ S, Ideal.absNorm v.asIdeal = n) → ∑ v ∈ S, pw F s v ≤ e n := by
    intro n S hS
    have hterm : ∀ v ∈ S, pw F s v = (n : ℝ) ^ (-s) := by
      intro v hv
      rw [pw, hS v hv]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, he]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    haveI : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 F) n).to_subtype
    have hle := Nat.card_le_card_of_injective
      (fun v : S => (⟨v.1.asIdeal, hS v.1 v.2⟩ : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}))
      (fun a b h => by
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext (HeightOneSpectrum.ext h))
    rw [Nat.card_eq_finsetCard] at hle
    exact_mod_cast hle
  calc ∑ n ∈ T.image (fun v => Ideal.absNorm v.asIdeal),
        ∑ v ∈ T with Ideal.absNorm v.asIdeal = n, pw F s v
      ≤ ∑ n ∈ T.image (fun v => Ideal.absNorm v.asIdeal), e n :=
        Finset.sum_le_sum fun n _ => hstep n _ (fun v hv => (Finset.mem_filter.mp hv).2)
    _ ≤ ∑' n, e n := h5.sum_le_tsum _ (fun n _ => by
        rw [he]
        exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem primeSum_toReal (s : ℝ) : (FrobeniusDensity.primeSum F s).toReal = ∑' v, pw F s v := by
  rw [FrobeniusDensity.primeSum, ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun v => ?_
    rw [FrobeniusDensity.normRpow, pw, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast]
  · intro v
    rw [FrobeniusDensity.normRpow, Ne, ENNReal.rpow_eq_top_iff]
    push Not
    constructor
    · intro h
      exfalso
      have := two_le_absNorm v
      have h' : Ideal.absNorm v.asIdeal = 0 := by exact_mod_cast h
      omega
    · intro h
      exact absurd h (ENNReal.natCast_ne_top _)

theorem tailSum_toReal (s : ℝ) : (FrobeniusDensity.tailSum F s).toReal =
    ∑' v, if (Ideal.absNorm v.asIdeal).Prime then 0 else pw F s v := by
  rw [FrobeniusDensity.tailSum, ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun v => ?_
    split_ifs
    · rfl
    · rw [FrobeniusDensity.normRpow, pw, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast]
  · intro v
    split_ifs
    · exact ENNReal.zero_ne_top
    · rw [FrobeniusDensity.normRpow, Ne, ENNReal.rpow_eq_top_iff]
      push Not
      constructor
      · intro h
        exfalso
        have := two_le_absNorm v
        have h' : Ideal.absNorm v.asIdeal = 0 := by exact_mod_cast h
        omega
      · intro h
        exact absurd h (ENNReal.natCast_ne_top _)

def invSq (n : ℕ) : NNReal := ((n : NNReal) ^ 2)⁻¹

theorem summable_invSq : Summable invSq := by
  rw [← NNReal.summable_coe]
  have : (fun n : ℕ => ((invSq n : NNReal) : ℝ)) = fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ := by
    funext n; simp [invSq]
  rw [this]
  exact Real.summable_nat_pow_inv.mpr one_lt_two

theorem tailConst_lt_top : FrobeniusDensity.tailConst < ⊤ := by
  rw [FrobeniusDensity.tailConst]
  have hle : (∑' ℓ : ℕ, (if ℓ.Prime then ((ℓ : ENNReal) ^ 2)⁻¹ else 0)) ≤
      ∑' ℓ : ℕ, ((invSq ℓ : NNReal) : ENNReal) := by
    refine ENNReal.tsum_le_tsum fun ℓ => ?_
    split_ifs with h
    · rw [invSq, ENNReal.coe_inv (pow_ne_zero _ (by exact_mod_cast h.ne_zero)), ENNReal.coe_pow,
        ENNReal.coe_natCast]
    · exact bot_le
  refine lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr ?_)
  rw [ENNReal.tsum_coe_ne_top_iff_summable]
  exact summable_invSq

variable (F) in

def Ctail : ℝ := ((Module.finrank ℚ F : ENNReal) * FrobeniusDensity.tailConst).toReal

theorem summable_tail {s : ℝ} (hs : 1 < s) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => if (Ideal.absNorm v.asIdeal).Prime then 0 else pw F s v := by
  refine (summable_pw hs).of_nonneg_of_le (fun v => ?_) (fun v => ?_)
  · split_ifs
    · exact le_rfl
    · exact pw_nonneg s v
  · split_ifs
    · exact pw_nonneg s v
    · exact le_rfl

theorem finite_bad : {v : HeightOneSpectrum (𝓞 F) | (m : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h : (Ideal.span {(m : 𝓞 F)} : Ideal (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast NeZero.ne m
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_span_singleton]
  exact hv

variable (F m) in

def nbad : ℕ := (finite_bad (F := F) (m := m)).toFinset.card

theorem tsum_bad_le (f : HeightOneSpectrum (𝓞 F) → ℝ) (hf : ∀ v, f v ≤ 1)
    (hsupp : ∀ v, (m : 𝓞 F) ∉ v.asIdeal → f v = 0) : ∑' v, f v ≤ nbad F m := by
  rw [tsum_eq_sum (s := (finite_bad (F := F) (m := m)).toFinset) (fun v hv => hsupp v (by
    rwa [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv))]
  calc ∑ v ∈ (finite_bad (F := F) (m := m)).toFinset, f v
      ≤ ∑ v ∈ (finite_bad (F := F) (m := m)).toFinset, (1 : ℝ) := Finset.sum_le_sum fun v _ => hf v
    _ = nbad F m := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, nbad]

end PrimeSums

section Residue

variable (F : Type) [Field F] [NumberField F] (m : ℕ) [NeZero m]

def T (a : ZMod m) (s : ℝ) : ℝ :=
  ∑' v : HeightOneSpectrum (𝓞 F), if (Ideal.absNorm v.asIdeal : ZMod m) = a then pw F s v else 0

def P0 (s : ℝ) : ℝ :=
  ∑' v : HeightOneSpectrum (𝓞 F), if (m : 𝓞 F) ∈ v.asIdeal then 0 else pw F s v

variable {F m}

theorem T_term_nonneg (a : ZMod m) (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    0 ≤ (if (Ideal.absNorm v.asIdeal : ZMod m) = a then pw F s v else 0) := by
  split_ifs
  · exact pw_nonneg s v
  · exact le_rfl

theorem T_term_le (a : ZMod m) (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    (if (Ideal.absNorm v.asIdeal : ZMod m) = a then pw F s v else 0) ≤ pw F s v := by
  split_ifs
  · exact le_rfl
  · exact pw_nonneg s v

theorem summable_T (a : ZMod m) {s : ℝ} (hs : 1 < s) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => if (Ideal.absNorm v.asIdeal : ZMod m) = a then pw F s v else 0 :=
  (summable_pw hs).of_nonneg_of_le (T_term_nonneg a s) (T_term_le a s)

theorem T_nonneg (a : ZMod m) (s : ℝ) : 0 ≤ T F m a s := tsum_nonneg (T_term_nonneg a s)

theorem P0_term_nonneg (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    0 ≤ (if (m : 𝓞 F) ∈ v.asIdeal then 0 else pw F s v) := by
  split_ifs
  · exact le_rfl
  · exact pw_nonneg s v

theorem P0_term_le (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    (if (m : 𝓞 F) ∈ v.asIdeal then 0 else pw F s v) ≤ pw F s v := by
  split_ifs
  · exact pw_nonneg s v
  · exact le_rfl

theorem summable_P0 {s : ℝ} (hs : 1 < s) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => if (m : 𝓞 F) ∈ v.asIdeal then 0 else pw F s v :=
  (summable_pw hs).of_nonneg_of_le (P0_term_nonneg s) (P0_term_le s)

theorem P0_le_tsum_pw {s : ℝ} (hs : 1 < s) : P0 F m s ≤ ∑' v, pw F s v :=
  (summable_P0 hs).tsum_le_tsum (P0_term_le s) (summable_pw hs)

theorem tsum_pw_le_P0_add {s : ℝ} (hs : 1 < s) : (∑' v, pw F s v) ≤ P0 F m s + nbad F m := by
  have hsplit : ∀ v : HeightOneSpectrum (𝓞 F), pw F s v =
      (if (m : 𝓞 F) ∈ v.asIdeal then 0 else pw F s v) + (if (m : 𝓞 F) ∈ v.asIdeal then pw F s v else 0) := by
    intro v; split_ifs <;> simp
  have hsum2 : Summable fun v : HeightOneSpectrum (𝓞 F) => if (m : 𝓞 F) ∈ v.asIdeal then pw F s v else 0 := by
    refine (summable_pw hs).of_nonneg_of_le (fun v => ?_) (fun v => ?_)
    · split_ifs
      · exact pw_nonneg s v
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact pw_nonneg s v
  rw [tsum_congr hsplit, (summable_P0 hs).tsum_add hsum2, P0]
  have hb := tsum_bad_le (F := F) (m := m) (fun v => if (m : 𝓞 F) ∈ v.asIdeal then pw F s v else 0)
    (fun v => by
      beta_reduce
      split_ifs
      · exact pw_le_one (by linarith) v
      · exact zero_le_one)
    (fun v hv => if_neg hv)
  linarith

end Residue

end NumberField.PrimeNormSum

end
