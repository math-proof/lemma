module

public import Theorem.Scheme.Correspondence
public import Abbrev.ModularCurve_XH

public noncomputable section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain

namespace ModularCurve

open AlgebraicCurve IntermediateField HahnSeries

section PrivateSupply

variable {L : Type*} [Field L] [Algebra ℚ L]

public theorem coeffMap_qExpandH {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]


public theorem coeffEmb_qExpandH (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) :=
  coeffMap_qExpandH _ n x

variable (L) in

public theorem laurentBaseChange_monoH {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)


public theorem qExpand_mem_laurentBaseChangeH {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ)
    [NeZero n] {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ y ∈ F₀, qExpand ℚ n y ∈ F₁)
    {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    qExpand L n x ∈ laurentBaseChange L F₁ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero,
          ← algebraMap_laurentSeries_eq_single]
        exact (laurentBaseChange L F₁).algebraMap_mem _
      · rw [← coeffEmb_qExpandH]
        exact coeffEmb_mem_laurentBaseChange L (hF z hz)
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

end PrivateSupply

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

section DegeneracyMaps

variable (L) in


@[simp]
public theorem coe_heckeAlphaHBar (x : laurentBaseChange L (xHFunctionField M H)) :
    (heckeAlphaHBar L M H ℓ x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

omit [NeZero ℓ] in


public theorem heckeAlphaHBar_eq_inclusion
    (h : laurentBaseChange L (xHFunctionField M H) ≤
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) :
    heckeAlphaHBar L M H ℓ = IntermediateField.inclusion h :=
  rfl


@[simp]
public theorem coe_heckeBetaHBarOf (h : HeckeBetaHDefined M H ℓ)
    (x : laurentBaseChange L (xHFunctionField M H)) :
    (heckeBetaHBarOf L M H ℓ h x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
  rfl

open Classical in
variable (L) in


public theorem heckeBetaHBar_eq (h : HeckeBetaHDefined M H ℓ) :
    (heckeBetaHBar L M H ℓ) = heckeBetaHBarOf L M H ℓ h := by
  rw [heckeBetaHBar, dif_pos h]


public theorem heckeBetaHBar_of_not (h : ¬ HeckeBetaHDefined M H ℓ) :
    (heckeBetaHBar L M H ℓ) = heckeAlphaHBar L M H ℓ := by
  rw [heckeBetaHBar, dif_neg h]


public theorem coe_heckeBetaHBar (h : HeckeBetaHDefined M H ℓ)
    (x : laurentBaseChange L (xHFunctionField M H)) :
    (heckeBetaHBar L M H ℓ x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) := by
  rw [heckeBetaHBar_eq M H ℓ h, coe_heckeBetaHBarOf]

end DegeneracyMaps

section HeckePic0HBar

variable (L) in


public theorem heckeInputsHAlong_intro (h0 : HeckeBetaHDefined M H ℓ)
    (hα : HeckeAlphaHBarIntegral L M H ℓ) (hβ : HeckeBetaHBarIntegral L M H ℓ)
    [hP : HasPrincipalDivisors L (laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (hFI : FundamentalIdentityAlong L (heckeBetaHBar L M H ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaHBar L M H ℓ))
    (hN : NormFormulaAlong L (heckeAlphaHBar L M H ℓ) hfin) : HeckeInputsHAlong L M H ℓ :=
  ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩


public theorem HeckeInputsHAlong.betaHDefined (h : HeckeInputsHAlong L M H ℓ) : HeckeBetaHDefined M H ℓ :=
  h.fst


public theorem heckeOperatorHAlong_eq (h0 : HeckeBetaHDefined M H ℓ)
    (hα : HeckeAlphaHBarIntegral L M H ℓ) (hβ : HeckeBetaHBarIntegral L M H ℓ)
    [HasPrincipalDivisors L (laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (hFI : FundamentalIdentityAlong L (heckeBetaHBar L M H ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaHBar L M H ℓ))
    (hN : NormFormulaAlong L (heckeAlphaHBar L M H ℓ) hfin) :
    heckeOperatorHAlong L M H ℓ = heckePic0HBar hα hβ hFI hfin hN := by
  have h : HeckeInputsHAlong L M H ℓ := heckeInputsHAlong_intro h0 hα hβ hFI hfin hN
  rw [heckeOperatorHAlong, dif_pos h]


public theorem heckeOperatorHAlong_of_not (h : ¬ HeckeInputsHAlong L M H ℓ) :
    heckeOperatorHAlong L M H ℓ = 0 := by
  rw [heckeOperatorHAlong, dif_neg h]

end Total

section ModularInstance

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

example :
    xHFunctionFieldBar M H →ₐ[AlgebraicClosure ℚ]
      laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ)) :=
  heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ

example : JH M H →+ JH M H :=
  heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ

end ModularInstance

end ModularCurve

end
