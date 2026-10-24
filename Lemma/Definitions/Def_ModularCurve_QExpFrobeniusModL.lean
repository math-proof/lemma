import Mathlib
import Lemma.Definitions.Def_ModularCurve_X1
import Lemma.Definitions.Def_ModularCurve_FrobeniusModL

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve Polynomial

namespace ModularCurve

section FrobeniusIdentity

variable (K : Type*) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

theorem coeff_intSeriesC_pow_char_eq (p : PowerSeries ℤ) (k : ℤ) :
    ((intSeriesC K p).coeff k) ^ ℓ = (intSeriesC K p).coeff k := by
  rcases lt_or_ge k 0 with hk | hk
  · rw [intSeriesC, ofPowerSeries_coeff_of_neg _ hk, zero_pow (Fact.out : ℓ.Prime).ne_zero]
  · lift k to ℕ using hk with k
    rw [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast]
    exact intCast_pow_char_eq K ℓ _

theorem coeffMap_frobenius_eq_self_of_coeff_fixed (s : LaurentSeries K)
    (hfix : ∀ k : ℤ, (s.coeff k) ^ ℓ = s.coeff k) : coeffMap (frobenius K ℓ) s = s := by
  ext k
  rw [coeffMap_coeff, frobenius_def, hfix]

omit [CharP K ℓ] in

theorem coeff_qExpand_pow_char_eq (s : LaurentSeries K) (hfix : ∀ k : ℤ, (s.coeff k) ^ ℓ = s.coeff k)
    (k : ℤ) : ((qExpand K ℓ s).coeff k) ^ ℓ = (qExpand K ℓ s).coeff k := by
  by_cases hk : (ℓ : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul]
    exact hfix m
  · rw [qExpand_coeff_of_not_dvd ℓ s hk, zero_pow (Fact.out : ℓ.Prime).ne_zero]

theorem qExpand_eq_pow_of_coeff_fixed (s : LaurentSeries K) (hfix : ∀ k : ℤ, (s.coeff k) ^ ℓ = s.coeff k) :
    qExpand K ℓ s = s ^ ℓ := by
  rw [pow_char_eq_coeffMap_frobenius_qExpand ℓ s,
    coeffMap_frobenius_eq_self_of_coeff_fixed K ℓ _ (coeff_qExpand_pow_char_eq K ℓ s hfix)]

theorem qExpand_intSeriesC_eq_pow (p : PowerSeries ℤ) :
    qExpand K ℓ (intSeriesC K p) = intSeriesC K p ^ ℓ :=
  qExpand_eq_pow_of_coeff_fixed K ℓ _ (coeff_intSeriesC_pow_char_eq K ℓ p)

end FrobeniusIdentity

section FrobeniusEndomorphism

variable (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

theorem qExpFrobeniusModL_map_le :
    (qExpFunctionFieldC K Γ).map (qExpandAlgHomC K ℓ) ≤ qExpFunctionFieldC K Γ := by
  rw [qExpFunctionFieldC, adjoin_map, adjoin_le_iff]
  rintro x ⟨y, ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
  show qExpandAlgHomC K ℓ (intSeriesC K pf / intSeriesC K pg) ∈ qExpFunctionFieldC K Γ
  rw [qExpandAlgHomC_apply, map_div₀, qExpand_intSeriesC_eq_pow, qExpand_intSeriesC_eq_pow, ← div_pow]
  exact pow_mem (div_mem_qExpFunctionFieldC f g hf hg hg0) ℓ

variable {K Γ ℓ} in
theorem qExpand_mem_qExpFunctionFieldC {x : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K Γ) :
    qExpand K ℓ x ∈ qExpFunctionFieldC K Γ :=
  qExpFrobeniusModL_map_le K Γ ℓ ⟨x, hx, rfl⟩

def qExpFrobeniusModLRingHom : qExpFunctionFieldC K Γ →+* qExpFunctionFieldC K Γ where
  toFun x := ⟨qExpand K ℓ (x : LaurentSeries K), qExpand_mem_qExpFunctionFieldC x.2⟩
  map_one' := Subtype.ext (map_one (qExpand K ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand K ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand K ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand K ℓ) _ _)

def qExpFrobeniusModL : qExpFunctionFieldC K Γ →ₐ[K] qExpFunctionFieldC K Γ :=
  { qExpFrobeniusModLRingHom K Γ ℓ with
    commutes' := fun a => Subtype.ext <| by
      show qExpand K ℓ (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

@[simp]
theorem coe_qExpFrobeniusModL (x : qExpFunctionFieldC K Γ) :
    (qExpFrobeniusModL K Γ ℓ x : LaurentSeries K) = qExpand K ℓ (x : LaurentSeries K) := rfl

theorem qExpFrobeniusModL_injective : Function.Injective (qExpFrobeniusModL K Γ ℓ) := fun _ _ h =>
  Subtype.ext (qExpand_injective ℓ (congrArg (fun z : qExpFunctionFieldC K Γ =>
    (z : LaurentSeries K)) h :))

theorem exists_qExpFrobeniusModL_eq_pow (x : qExpFunctionFieldC K Γ) :
    ∃ y : qExpFunctionFieldC K Γ, qExpFrobeniusModL K Γ ℓ y = x ^ ℓ := by
  haveI : CharP (LaurentSeries K) ℓ := charP_laurentSeriesC K ℓ
  suffices h : ∀ {z : LaurentSeries K}, z ∈ qExpFunctionFieldC K Γ →
      ∃ y : LaurentSeries K, y ∈ qExpFunctionFieldC K Γ ∧ qExpand K ℓ y = z ^ ℓ by
    obtain ⟨y, hy, hyx⟩ := h x.2
    exact ⟨⟨y, hy⟩, Subtype.ext (by rw [coe_qExpFrobeniusModL]; push_cast; exact hyx)⟩
  intro z hz
  induction hz using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
    refine ⟨intSeriesC K pf / intSeriesC K pg, div_mem_qExpFunctionFieldC f g hf hg hg0, ?_⟩
    rw [map_div₀, qExpand_intSeriesC_eq_pow, qExpand_intSeriesC_eq_pow, div_pow]
  | algebraMap c =>
    refine ⟨algebraMap K (LaurentSeries K) (c ^ ℓ), (qExpFunctionFieldC K Γ).algebraMap_mem _, ?_⟩
    rw [map_pow, map_pow, algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
  | add y z _ _ hy hz =>
    obtain ⟨y', hy', hyy⟩ := hy
    obtain ⟨z', hz', hzz⟩ := hz
    exact ⟨y' + z', add_mem hy' hz', by rw [map_add, hyy, hzz, add_pow_char]⟩
  | inv y _ hy =>
    obtain ⟨y', hy', hyy⟩ := hy
    exact ⟨y'⁻¹, inv_mem hy', by rw [map_inv₀, hyy, inv_pow]⟩
  | mul y z _ _ hy hz =>
    obtain ⟨y', hy', hyy⟩ := hy
    obtain ⟨z', hz', hzz⟩ := hz
    exact ⟨y' * z', mul_mem hy' hz', by rw [map_mul, hyy, hzz, mul_pow]⟩

theorem qExpFrobeniusModL_isIntegral : (qExpFrobeniusModL K Γ ℓ).toRingHom.IsIntegral := by
  intro x
  obtain ⟨y, hy⟩ := exists_qExpFrobeniusModL_eq_pow K Γ ℓ x
  refine ⟨Polynomial.X ^ ℓ - Polynomial.C y, Polynomial.monic_X_pow_sub_C _ (Fact.out : ℓ.Prime).ne_zero, ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero]
  exact hy.symm

end FrobeniusEndomorphism

section PlacesDivisors

variable (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

def qExpFrobeniusPlaceModL (w : Place K (qExpFunctionFieldC K Γ)) : Place K (qExpFunctionFieldC K Γ) :=
  w.restrictAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)

theorem mem_qExpFrobeniusPlaceModL_iff (w : Place K (qExpFunctionFieldC K Γ)) (x : qExpFunctionFieldC K Γ) :
    x ∈ (qExpFrobeniusPlaceModL K Γ ℓ w).toValuationSubring ↔
      qExpFrobeniusModL K Γ ℓ x ∈ w.toValuationSubring :=
  Iff.rfl

def qExpFrobeniusDivPushforwardModL :
    Divisor K (qExpFunctionFieldC K Γ) →+ Divisor K (qExpFunctionFieldC K Γ) :=
  Divisor.pushforwardAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)

def qExpFrobeniusDivPullbackModL [HasPrincipalDivisors K (qExpFunctionFieldC K Γ)] :
    Divisor K (qExpFunctionFieldC K Γ) →+ Divisor K (qExpFunctionFieldC K Γ) :=
  Divisor.pullbackAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)

theorem qExpFrobeniusDivPushforwardModL_single (w : Place K (qExpFunctionFieldC K Γ)) (n : ℤ) :
    qExpFrobeniusDivPushforwardModL K Γ ℓ (Finsupp.single w n) =
      Finsupp.single (qExpFrobeniusPlaceModL K Γ ℓ w)
        (n * w.inertiaDegAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)) :=
  Divisor.pushforwardAlong_single (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) w n

theorem degree_qExpFrobeniusDivPushforwardModL (D : Divisor K (qExpFunctionFieldC K Γ)) :
    Divisor.degree (qExpFrobeniusDivPushforwardModL K Γ ℓ D) = Divisor.degree D :=
  Divisor.degree_pushforwardAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) D

end PlacesDivisors

section Jacobian

variable (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

def QExpFrobeniusInputsModL : Prop :=
  ∃ (_ : HasPrincipalDivisors K (qExpFunctionFieldC K Γ))
    (hfin : FiniteAlong K (qExpFrobeniusModL K Γ ℓ)),
    FundamentalIdentityAlong K (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) ∧
      NormFormulaAlong K (qExpFrobeniusModL K Γ ℓ) hfin

variable {K Γ ℓ} in

theorem qExpFrobeniusInputsModL_intro [hP : HasPrincipalDivisors K (qExpFunctionFieldC K Γ)]
    (hfin : FiniteAlong K (qExpFrobeniusModL K Γ ℓ))
    (hFI : FundamentalIdentityAlong K (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ))
    (hN : NormFormulaAlong K (qExpFrobeniusModL K Γ ℓ) hfin) : QExpFrobeniusInputsModL K Γ ℓ :=
  ⟨hP, hfin, hFI, hN⟩

def qExpFrobeniusDegZeroPushforwardModL :
    Divisor.degZero (K := K) (F := qExpFunctionFieldC K Γ) →+
      Divisor.degZero (K := K) (F := qExpFunctionFieldC K Γ) :=
  ((qExpFrobeniusDivPushforwardModL K Γ ℓ).domRestrict _).codRestrict _
    fun D => Divisor.pushforwardAlong_mem_degZero (qExpFrobeniusModL K Γ ℓ)
      (qExpFrobeniusModL_isIntegral K Γ ℓ) D.2

@[simp]
theorem coe_qExpFrobeniusDegZeroPushforwardModL
    (D : Divisor.degZero (K := K) (F := qExpFunctionFieldC K Γ)) :
    (qExpFrobeniusDegZeroPushforwardModL K Γ ℓ D : Divisor K (qExpFunctionFieldC K Γ)) =
      qExpFrobeniusDivPushforwardModL K Γ ℓ D :=
  rfl

def qExpFrobeniusDegZeroPullbackModL [HasPrincipalDivisors K (qExpFunctionFieldC K Γ)]
    (hFI : FundamentalIdentityAlong K (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)) :
    Divisor.degZero (K := K) (F := qExpFunctionFieldC K Γ) →+
      Divisor.degZero (K := K) (F := qExpFunctionFieldC K Γ) :=
  ((qExpFrobeniusDivPullbackModL K Γ ℓ).domRestrict _).codRestrict _
    fun D => Divisor.pullbackAlong_mem_degZero (qExpFrobeniusModL K Γ ℓ)
      (qExpFrobeniusModL_isIntegral K Γ ℓ) hFI D.2

@[simp]
theorem coe_qExpFrobeniusDegZeroPullbackModL [HasPrincipalDivisors K (qExpFunctionFieldC K Γ)]
    (hFI : FundamentalIdentityAlong K (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ))
    (D : Divisor.degZero (K := K) (F := qExpFunctionFieldC K Γ)) :
    (qExpFrobeniusDegZeroPullbackModL K Γ ℓ hFI D : Divisor K (qExpFunctionFieldC K Γ)) =
      qExpFrobeniusDivPullbackModL K Γ ℓ D :=
  rfl

def qExpFrobeniusPic0PushforwardModL (hfin : FiniteAlong K (qExpFrobeniusModL K Γ ℓ))
    (hN : NormFormulaAlong K (qExpFrobeniusModL K Γ ℓ) hfin) :
    Pic0 K (qExpFunctionFieldC K Γ) →+ Pic0 K (qExpFunctionFieldC K Γ) :=
  QuotientAddGroup.map _ _ (qExpFrobeniusDegZeroPushforwardModL K Γ ℓ) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pushforwardAlong (qExpFrobeniusModL K Γ ℓ)
      (qExpFrobeniusModL_isIntegral K Γ ℓ) hfin hN hD)

theorem qExpFrobeniusPic0PushforwardModL_mk (hfin : FiniteAlong K (qExpFrobeniusModL K Γ ℓ))
    (hN : NormFormulaAlong K (qExpFrobeniusModL K Γ ℓ) hfin)
    (D : Divisor.degZero (K := K) (F := qExpFunctionFieldC K Γ)) :
    qExpFrobeniusPic0PushforwardModL K Γ ℓ hfin hN (Pic0.mk D) =
      Pic0.mk (qExpFrobeniusDegZeroPushforwardModL K Γ ℓ D) :=
  rfl

def qExpFrobeniusPic0PullbackModL [HasPrincipalDivisors K (qExpFunctionFieldC K Γ)]
    (hFI : FundamentalIdentityAlong K (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)) :
    Pic0 K (qExpFunctionFieldC K Γ) →+ Pic0 K (qExpFunctionFieldC K Γ) :=
  QuotientAddGroup.map _ _ (qExpFrobeniusDegZeroPullbackModL K Γ ℓ hFI) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pullbackAlong (qExpFrobeniusModL K Γ ℓ)
      (qExpFrobeniusModL_isIntegral K Γ ℓ) hD)

theorem qExpFrobeniusPic0PullbackModL_mk [HasPrincipalDivisors K (qExpFunctionFieldC K Γ)]
    (hFI : FundamentalIdentityAlong K (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ))
    (D : Divisor.degZero (K := K) (F := qExpFunctionFieldC K Γ)) :
    qExpFrobeniusPic0PullbackModL K Γ ℓ hFI (Pic0.mk D) =
      Pic0.mk (qExpFrobeniusDegZeroPullbackModL K Γ ℓ hFI D) :=
  rfl

open Classical in

def qExpFrobeniusPushforwardModL : Pic0 K (qExpFunctionFieldC K Γ) →+ Pic0 K (qExpFunctionFieldC K Γ) :=
  if h : QExpFrobeniusInputsModL K Γ ℓ then
    qExpFrobeniusPic0PushforwardModL K Γ ℓ h.snd.fst h.snd.snd.2
  else 0

open Classical in

def qExpFrobeniusPullbackModL : Pic0 K (qExpFunctionFieldC K Γ) →+ Pic0 K (qExpFunctionFieldC K Γ) :=
  if h : QExpFrobeniusInputsModL K Γ ℓ then
    haveI := h.fst
    qExpFrobeniusPic0PullbackModL K Γ ℓ h.snd.snd.1
  else 0

variable {K Γ ℓ}

theorem qExpFrobeniusPushforwardModL_eq [HasPrincipalDivisors K (qExpFunctionFieldC K Γ)]
    (hfin : FiniteAlong K (qExpFrobeniusModL K Γ ℓ))
    (hFI : FundamentalIdentityAlong K (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ))
    (hN : NormFormulaAlong K (qExpFrobeniusModL K Γ ℓ) hfin) :
    qExpFrobeniusPushforwardModL K Γ ℓ = qExpFrobeniusPic0PushforwardModL K Γ ℓ hfin hN := by
  have h : QExpFrobeniusInputsModL K Γ ℓ := qExpFrobeniusInputsModL_intro hfin hFI hN
  rw [qExpFrobeniusPushforwardModL, dif_pos h]

theorem qExpFrobeniusPushforwardModL_mk [HasPrincipalDivisors K (qExpFunctionFieldC K Γ)]
    (hfin : FiniteAlong K (qExpFrobeniusModL K Γ ℓ))
    (hFI : FundamentalIdentityAlong K (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ))
    (hN : NormFormulaAlong K (qExpFrobeniusModL K Γ ℓ) hfin)
    (D : Divisor.degZero (K := K) (F := qExpFunctionFieldC K Γ)) :
    qExpFrobeniusPushforwardModL K Γ ℓ (Pic0.mk D) = Pic0.mk (qExpFrobeniusDegZeroPushforwardModL K Γ ℓ D) := by
  rw [qExpFrobeniusPushforwardModL_eq hfin hFI hN]
  rfl

theorem qExpFrobeniusPushforwardModL_of_not (h : ¬ QExpFrobeniusInputsModL K Γ ℓ) :
    qExpFrobeniusPushforwardModL K Γ ℓ = 0 := by
  rw [qExpFrobeniusPushforwardModL, dif_neg h]

theorem qExpFrobeniusPullbackModL_eq [HasPrincipalDivisors K (qExpFunctionFieldC K Γ)]
    (hfin : FiniteAlong K (qExpFrobeniusModL K Γ ℓ))
    (hFI : FundamentalIdentityAlong K (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ))
    (hN : NormFormulaAlong K (qExpFrobeniusModL K Γ ℓ) hfin) :
    qExpFrobeniusPullbackModL K Γ ℓ = qExpFrobeniusPic0PullbackModL K Γ ℓ hFI := by
  have h : QExpFrobeniusInputsModL K Γ ℓ := qExpFrobeniusInputsModL_intro hfin hFI hN
  rw [qExpFrobeniusPullbackModL, dif_pos h]

theorem qExpFrobeniusPullbackModL_mk [HasPrincipalDivisors K (qExpFunctionFieldC K Γ)]
    (hfin : FiniteAlong K (qExpFrobeniusModL K Γ ℓ))
    (hFI : FundamentalIdentityAlong K (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ))
    (hN : NormFormulaAlong K (qExpFrobeniusModL K Γ ℓ) hfin)
    (D : Divisor.degZero (K := K) (F := qExpFunctionFieldC K Γ)) :
    qExpFrobeniusPullbackModL K Γ ℓ (Pic0.mk D) = Pic0.mk (qExpFrobeniusDegZeroPullbackModL K Γ ℓ hFI D) := by
  rw [qExpFrobeniusPullbackModL_eq hfin hFI hN]
  rfl

theorem qExpFrobeniusPullbackModL_of_not (h : ¬ QExpFrobeniusInputsModL K Γ ℓ) :
    qExpFrobeniusPullbackModL K Γ ℓ = 0 := by
  rw [qExpFrobeniusPullbackModL, dif_neg h]

example (M : ℕ) : (JOneC M K →+ JOneC M K) :=
  qExpFrobeniusPushforwardModL K (CongruenceSubgroup.Gamma1 M) ℓ

example (M : ℕ) (y : JOneC M K) : JOneC M K :=
  qExpFrobeniusPullbackModL K (CongruenceSubgroup.Gamma1 M) ℓ
    (qExpFrobeniusPushforwardModL K (CongruenceSubgroup.Gamma1 M) ℓ y)

end Jacobian

end ModularCurve

end
