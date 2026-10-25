import Mathlib
import Lemma.ModularCurve.X1

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IntermediateField HahnSeries CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

section CoeffMapLemmas

variable {K K' : Type*} [Field K] [Field K']

theorem coeffMap_intSeriesC (τ : K →+* K') (p : PowerSeries ℤ) :
    coeffMap τ (intSeriesC K p) = intSeriesC K' p := by
  ext k
  rw [coeffMap_coeff]
  rcases lt_or_ge k 0 with hk | hk
  · rw [intSeriesC, intSeriesC, ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk,
      map_zero]
  · lift k to ℕ using hk with k
    rw [intSeriesC, intSeriesC, HahnSeries.ofPowerSeries_apply_coeff,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast,
      eq_intCast, map_intCast]

theorem coeffMap_mem_intFormRatiosC_of_mem (τ : K →+* K') (Γ : Subgroup SL(2, ℤ))
    {x : LaurentSeries K} (hx : x ∈ intFormRatiosC K Γ) :
    coeffMap τ x ∈ intFormRatiosC K' Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  have hg0' : intSeriesC K' pg ≠ 0 := by
    intro h
    apply hg0
    have h' : coeffMap τ (intSeriesC K pg) = 0 := by rw [coeffMap_intSeriesC, h]
    ext n
    have hn := congrArg (fun s : LaurentSeries K' => s.coeff n) h'
    simp only [coeffMap_coeff] at hn
    rw [HahnSeries.coeff_zero] at hn ⊢
    exact (map_eq_zero τ).mp hn
  refine ⟨k, f, g, pf, pg, hf, hg, hg0', ?_⟩
  rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

theorem coeffMap_mem_qExpFunctionFieldC_of_mem (τ : K →+* K') (Γ : Subgroup SL(2, ℤ))
    {x : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K Γ) :
    coeffMap τ x ∈ qExpFunctionFieldC K' Γ := by
  change x ∈ (IntermediateField.adjoin K (intFormRatiosC K Γ)).toSubfield at hx
  rw [IntermediateField.adjoin_toSubfield] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hy
      · have e : coeffMap τ (algebraMap K (LaurentSeries K) a) = algebraMap K' (LaurentSeries K') (τ a) := by
          rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]
        rw [e]
        exact (qExpFunctionFieldC K' Γ).algebraMap_mem _
      · exact intFormRatiosC_subset K' Γ (coeffMap_mem_intFormRatiosC_of_mem τ Γ hy)
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

theorem coeffMap_mem_qExpFunctionFieldC (τ : K →+* K) (Γ : Subgroup SL(2, ℤ))
    {x : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K Γ) :
    coeffMap τ x ∈ qExpFunctionFieldC K Γ :=
  coeffMap_mem_qExpFunctionFieldC_of_mem τ Γ hx

end CoeffMapLemmas

section CoeffAut

variable {K : Type*} [Field K] (Γ : Subgroup SL(2, ℤ))

def qExpCoeffRingAut (τ : K ≃+* K) : qExpFunctionFieldC K Γ ≃+* qExpFunctionFieldC K Γ where
  toFun x := ⟨coeffMap (τ : K →+* K) (x : LaurentSeries K),
    coeffMap_mem_qExpFunctionFieldC (τ : K →+* K) Γ x.2⟩
  invFun x := ⟨coeffMap (τ.symm : K →+* K) (x : LaurentSeries K),
    coeffMap_mem_qExpFunctionFieldC (τ.symm : K →+* K) Γ x.2⟩
  left_inv x := Subtype.ext <| by
    show coeffMap (τ.symm : K →+* K) (coeffMap (τ : K →+* K) (x : LaurentSeries K))
      = (x : LaurentSeries K)
    rw [coeffMap_coeffMap,
      coeffMap_congr (g := RingHom.id K) (RingHom.ext fun a => τ.symm_apply_apply a) _, coeffMap_id]
  right_inv x := Subtype.ext <| by
    show coeffMap (τ : K →+* K) (coeffMap (τ.symm : K →+* K) (x : LaurentSeries K))
      = (x : LaurentSeries K)
    rw [coeffMap_coeffMap,
      coeffMap_congr (g := RingHom.id K) (RingHom.ext fun a => τ.apply_symm_apply a) _, coeffMap_id]
  map_mul' x y :=
    Subtype.ext (map_mul (coeffMap (τ : K →+* K)) (x : LaurentSeries K) (y : LaurentSeries K))
  map_add' x y :=
    Subtype.ext (map_add (coeffMap (τ : K →+* K)) (x : LaurentSeries K) (y : LaurentSeries K))

@[simp]
theorem coe_qExpCoeffRingAut_apply (τ : K ≃+* K) (x : qExpFunctionFieldC K Γ) :
    (qExpCoeffRingAut Γ τ x : LaurentSeries K) = coeffMap (τ : K →+* K) (x : LaurentSeries K) :=
  rfl

theorem qExpCoeffRingAut_algebraMap (τ : K ≃+* K) (a : K) :
    qExpCoeffRingAut Γ τ (algebraMap K (qExpFunctionFieldC K Γ) a)
      = algebraMap K (qExpFunctionFieldC K Γ) (τ a) :=
  Subtype.ext (coeffMap_algebraMap (τ : K →+* K) a)

def qExpCoeffSemilinearAut (τ : K ≃+* K) : SemilinearAut K (qExpFunctionFieldC K Γ) :=
  ⟨(qExpCoeffRingAut Γ τ, τ), fun a => qExpCoeffRingAut_algebraMap Γ τ a⟩

@[simp]
theorem toRingAut_qExpCoeffSemilinearAut (τ : K ≃+* K) :
    SemilinearAut.toRingAut (qExpCoeffSemilinearAut Γ τ) = qExpCoeffRingAut Γ τ := rfl

@[simp]
theorem baseAut_qExpCoeffSemilinearAut (τ : K ≃+* K) :
    SemilinearAut.baseAut (qExpCoeffSemilinearAut Γ τ) = τ := rfl

theorem coe_qExpCoeffSemilinearAut_smul (τ : K ≃+* K) (x : qExpFunctionFieldC K Γ) :
    ((qExpCoeffSemilinearAut Γ τ • x : qExpFunctionFieldC K Γ) : LaurentSeries K)
      = coeffMap (τ : K →+* K) (x : LaurentSeries K) := rfl

theorem coeff_qExpCoeffSemilinearAut_smul (τ : K ≃+* K) (x : qExpFunctionFieldC K Γ) (n : ℤ) :
    ((qExpCoeffSemilinearAut Γ τ • x : qExpFunctionFieldC K Γ) : LaurentSeries K).coeff n
      = τ ((x : LaurentSeries K).coeff n) := rfl

theorem qExpCoeffSemilinearAut_smul_eq_self_of_coe_eq_intSeriesC_div (τ : K ≃+* K)
    (x : qExpFunctionFieldC K Γ) (pf pg : PowerSeries ℤ)
    (hx : (x : LaurentSeries K) = intSeriesC K pf / intSeriesC K pg) :
    qExpCoeffSemilinearAut Γ τ • x = x :=
  Subtype.ext <| by
    rw [coe_qExpCoeffSemilinearAut_smul, hx, map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

def qExpCoeffSemilinearAutHom : (K ≃+* K) →* SemilinearAut K (qExpFunctionFieldC K Γ) where
  toFun τ := qExpCoeffSemilinearAut Γ τ
  map_one' := by
    refine Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext ?_) rfl)
    show coeffMap ((1 : K ≃+* K) : K →+* K) (x : LaurentSeries K) = (x : LaurentSeries K)
    rw [show ((1 : K ≃+* K) : K →+* K) = RingHom.id K from RingHom.ext fun _ => rfl, coeffMap_id]
  map_mul' σ τ := by
    refine Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext ?_) rfl)
    show coeffMap ((σ * τ : K ≃+* K) : K →+* K) (x : LaurentSeries K)
      = coeffMap (σ : K →+* K) (coeffMap (τ : K →+* K) (x : LaurentSeries K))
    rw [coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext fun _ => rfl) _

@[simp]
theorem qExpCoeffSemilinearAutHom_apply (τ : K ≃+* K) :
    qExpCoeffSemilinearAutHom Γ τ = qExpCoeffSemilinearAut Γ τ := rfl

theorem eq_qExpCoeffSemilinearAut_smul_of_coeff_eq (τ : K ≃+* K)
    (g : SemilinearAut K (qExpFunctionFieldC K Γ))
    (hg : ∀ (x : qExpFunctionFieldC K Γ) (n : ℤ),
      ((g • x : qExpFunctionFieldC K Γ) : LaurentSeries K).coeff n = τ ((x : LaurentSeries K).coeff n))
    (x : qExpFunctionFieldC K Γ) :
    g • x = qExpCoeffSemilinearAut Γ τ • x :=
  Subtype.ext (HahnSeries.ext (funext fun n => by rw [hg, coeff_qExpCoeffSemilinearAut_smul]))

theorem baseAut_eq_of_coeff_eq (τ : K ≃+* K) (g : SemilinearAut K (qExpFunctionFieldC K Γ))
    (hg : ∀ (x : qExpFunctionFieldC K Γ) (n : ℤ),
      ((g • x : qExpFunctionFieldC K Γ) : LaurentSeries K).coeff n = τ ((x : LaurentSeries K).coeff n))
    (a : K) : SemilinearAut.baseAut g a = τ a := by
  have hcoe : ∀ b : K,
      ((algebraMap K (qExpFunctionFieldC K Γ) b : qExpFunctionFieldC K Γ) : LaurentSeries K).coeff 0
        = b := fun b => by
    have e : ((algebraMap K (qExpFunctionFieldC K Γ) b : qExpFunctionFieldC K Γ) : LaurentSeries K)
        = algebraMap K (LaurentSeries K) b :=
      IntermediateField.coe_algebraMap_apply (qExpFunctionFieldC K Γ) b
    rw [e, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_same]
  have h₁ := hg (algebraMap K (qExpFunctionFieldC K Γ) a) 0
  rw [SemilinearAut.smul_algebraMap, hcoe, hcoe] at h₁
  exact h₁

theorem eq_qExpCoeffSemilinearAut_of_coeff_eq (τ : K ≃+* K)
    (g : SemilinearAut K (qExpFunctionFieldC K Γ))
    (hg : ∀ (x : qExpFunctionFieldC K Γ) (n : ℤ),
      ((g • x : qExpFunctionFieldC K Γ) : LaurentSeries K).coeff n = τ ((x : LaurentSeries K).coeff n)) :
    g = qExpCoeffSemilinearAut Γ τ :=
  Subtype.ext (Prod.ext
    (RingEquiv.ext fun x => eq_qExpCoeffSemilinearAut_smul_of_coeff_eq Γ τ g hg x)
    (RingEquiv.ext fun a => baseAut_eq_of_coeff_eq Γ τ g hg a))

end CoeffAut

section Frobenius

variable (p : ℕ) (K : Type*) [Field K] [Fact p.Prime] [CharP K p] [PerfectField K]
  (Γ : Subgroup SL(2, ℤ))

def qExpArithFrobC : SemilinearAut K (qExpFunctionFieldC K Γ) :=
  qExpCoeffSemilinearAut Γ (frobeniusEquiv K p)

@[simp]
theorem baseAut_qExpArithFrobC_apply (a : K) :
    SemilinearAut.baseAut (qExpArithFrobC p K Γ) a = a ^ p :=
  frobeniusEquiv_apply K p a

theorem coe_qExpArithFrobC_smul (x : qExpFunctionFieldC K Γ) :
    ((qExpArithFrobC p K Γ • x : qExpFunctionFieldC K Γ) : LaurentSeries K)
      = coeffMap (frobenius K p) (x : LaurentSeries K) := rfl

theorem coeff_qExpArithFrobC_smul (x : qExpFunctionFieldC K Γ) (n : ℤ) :
    ((qExpArithFrobC p K Γ • x : qExpFunctionFieldC K Γ) : LaurentSeries K).coeff n
      = ((x : LaurentSeries K).coeff n) ^ p :=
  frobenius_def (R := K) p _

theorem qExpArithFrobC_smul_eq_self_of_coeff_pow_eq (x : qExpFunctionFieldC K Γ)
    (hx : ∀ n : ℤ, ((x : LaurentSeries K).coeff n) ^ p = (x : LaurentSeries K).coeff n) :
    qExpArithFrobC p K Γ • x = x :=
  Subtype.ext (HahnSeries.ext (funext fun n => by rw [coeff_qExpArithFrobC_smul, hx]))

theorem qExpArithFrobC_smul_eq_self_of_coe_eq_intSeriesC_div (x : qExpFunctionFieldC K Γ)
    (pf pg : PowerSeries ℤ) (hx : (x : LaurentSeries K) = intSeriesC K pf / intSeriesC K pg) :
    qExpArithFrobC p K Γ • x = x :=
  qExpCoeffSemilinearAut_smul_eq_self_of_coe_eq_intSeriesC_div Γ _ x pf pg hx

theorem eq_qExpArithFrobC_smul_of_coeff_eq (g : SemilinearAut K (qExpFunctionFieldC K Γ))
    (hg : ∀ (x : qExpFunctionFieldC K Γ) (n : ℤ),
      ((g • x : qExpFunctionFieldC K Γ) : LaurentSeries K).coeff n = ((x : LaurentSeries K).coeff n) ^ p)
    (x : qExpFunctionFieldC K Γ) :
    g • x = qExpArithFrobC p K Γ • x :=
  eq_qExpCoeffSemilinearAut_smul_of_coeff_eq Γ _ g
    (fun y n => by rw [hg]; exact (frobeniusEquiv_apply K p _).symm) x

theorem eq_qExpArithFrobC_of_coeff_eq (g : SemilinearAut K (qExpFunctionFieldC K Γ))
    (hg : ∀ (x : qExpFunctionFieldC K Γ) (n : ℤ),
      ((g • x : qExpFunctionFieldC K Γ) : LaurentSeries K).coeff n = ((x : LaurentSeries K).coeff n) ^ p) :
    g = qExpArithFrobC p K Γ :=
  eq_qExpCoeffSemilinearAut_of_coeff_eq Γ _ g
    (fun y n => by rw [hg]; exact (frobeniusEquiv_apply K p _).symm)

end Frobenius

section LevelCarriers

variable (p : ℕ) (K : Type*) [Field K] [Fact p.Prime] [CharP K p] [PerfectField K] (M : ℕ)

def x1ArithFrobC : SemilinearAut K (x1FunctionFieldC K M) :=
  qExpArithFrobC p K (Gamma1 M)

theorem x1ArithFrobC_eq : x1ArithFrobC p K M = qExpArithFrobC p K (Gamma1 M) := rfl

@[simp]
theorem baseAut_x1ArithFrobC_apply (a : K) :
    SemilinearAut.baseAut (x1ArithFrobC p K M) a = a ^ p :=
  baseAut_qExpArithFrobC_apply p K _ a

theorem coe_x1ArithFrobC_smul (x : x1FunctionFieldC K M) :
    ((x1ArithFrobC p K M • x : x1FunctionFieldC K M) : LaurentSeries K)
      = coeffMap (frobenius K p) (x : LaurentSeries K) := rfl

theorem coeff_x1ArithFrobC_smul (x : x1FunctionFieldC K M) (n : ℤ) :
    ((x1ArithFrobC p K M • x : x1FunctionFieldC K M) : LaurentSeries K).coeff n
      = ((x : LaurentSeries K).coeff n) ^ p :=
  coeff_qExpArithFrobC_smul p K _ x n

def x1x0ArithFrobC (t : ℕ) : SemilinearAut K (x1x0FunctionFieldC K M t) :=
  qExpArithFrobC p K (Gamma1 M ⊓ Gamma0 t)

theorem x1x0ArithFrobC_eq (t : ℕ) :
    x1x0ArithFrobC p K M t =
      qExpArithFrobC p K (Gamma1 M ⊓ Gamma0 t) := rfl

@[simp]
theorem baseAut_x1x0ArithFrobC_apply (t : ℕ) (a : K) :
    SemilinearAut.baseAut (x1x0ArithFrobC p K M t) a = a ^ p :=
  baseAut_qExpArithFrobC_apply p K _ a

theorem coe_x1x0ArithFrobC_smul (t : ℕ) (x : x1x0FunctionFieldC K M t) :
    ((x1x0ArithFrobC p K M t • x : x1x0FunctionFieldC K M t) : LaurentSeries K)
      = coeffMap (frobenius K p) (x : LaurentSeries K) := rfl

theorem coeff_x1x0ArithFrobC_smul (t : ℕ) (x : x1x0FunctionFieldC K M t) (n : ℤ) :
    ((x1x0ArithFrobC p K M t • x : x1x0FunctionFieldC K M t) : LaurentSeries K).coeff n
      = ((x : LaurentSeries K).coeff n) ^ p :=
  coeff_qExpArithFrobC_smul p K _ x n

end LevelCarriers

end ModularCurve

end
