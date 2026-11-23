module

public import Theorem.Scheme.Correspondence
public import Theorem.UpperHalfPlane.X1

public noncomputable section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain

namespace ModularCurve

open AlgebraicCurve IntermediateField HahnSeries

section PrivateSupply

variable {L : Type*} [Field L] [Algebra ℚ L]

public theorem coeffMap_qExpand₁ {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]


public theorem coeffEmb_qExpand₁ (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) :=
  coeffMap_qExpand₁ _ n x

variable (L) in

public theorem laurentBaseChange_mono₁ {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)


public theorem qExpand_mem_laurentBaseChange₁ {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ)
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
      · rw [← coeffEmb_qExpand₁]
        exact coeffEmb_mem_laurentBaseChange L (hF z hz)
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

end PrivateSupply

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (M ℓ : ℕ) [NeZero ℓ]

section DegeneracyMaps

variable (L) in


@[simp]
public theorem coe_heckeAlphaOneBar (x : laurentBaseChange L (x1FunctionField M)) :
    (heckeAlphaOneBar L M ℓ x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

omit [NeZero ℓ] in


public theorem heckeAlphaOneBar_eq_inclusion
    (h : laurentBaseChange L (x1FunctionField M) ≤ laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) :
    heckeAlphaOneBar L M ℓ = IntermediateField.inclusion h :=
  rfl


@[simp]
public theorem coe_heckeBetaOneBarOf (h : HeckeBetaOneDefined M ℓ) (x : laurentBaseChange L (x1FunctionField M)) :
    (heckeBetaOneBarOf L M ℓ h x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
  rfl

open Classical in
variable (L) in


public theorem heckeBetaOneBar_eq (h : HeckeBetaOneDefined M ℓ) :
    (heckeBetaOneBar L M ℓ) = heckeBetaOneBarOf L M ℓ h := by
  rw [heckeBetaOneBar, dif_pos h]


public theorem heckeBetaOneBar_of_not (h : ¬ HeckeBetaOneDefined M ℓ) :
    (heckeBetaOneBar L M ℓ) = heckeAlphaOneBar L M ℓ := by
  rw [heckeBetaOneBar, dif_neg h]


public theorem coe_heckeBetaOneBar (h : HeckeBetaOneDefined M ℓ) (x : laurentBaseChange L (x1FunctionField M)) :
    (heckeBetaOneBar L M ℓ x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) := by
  rw [heckeBetaOneBar_eq M ℓ h, coe_heckeBetaOneBarOf]

end DegeneracyMaps

section HeckePic0OneBar

variable (L) in


public theorem heckeInputsOneAlong_intro (h0 : HeckeBetaOneDefined M ℓ)
    (hα : HeckeAlphaOneBarIntegral L M ℓ) (hβ : HeckeBetaOneBarIntegral L M ℓ)
    [hP : HasPrincipalDivisors L (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)))]
    (hFI : FundamentalIdentityAlong L (heckeBetaOneBar L M ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaOneBar L M ℓ))
    (hN : NormFormulaAlong L (heckeAlphaOneBar L M ℓ) hfin) : HeckeInputsOneAlong L M ℓ :=
  ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩


public theorem HeckeInputsOneAlong.betaOneDefined (h : HeckeInputsOneAlong L M ℓ) : HeckeBetaOneDefined M ℓ :=
  h.fst


public theorem heckeOperatorOneAlong_eq (h0 : HeckeBetaOneDefined M ℓ)
    (hα : HeckeAlphaOneBarIntegral L M ℓ) (hβ : HeckeBetaOneBarIntegral L M ℓ)
    [HasPrincipalDivisors L (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)))]
    (hFI : FundamentalIdentityAlong L (heckeBetaOneBar L M ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaOneBar L M ℓ))
    (hN : NormFormulaAlong L (heckeAlphaOneBar L M ℓ) hfin) :
    heckeOperatorOneAlong L M ℓ = heckePic0OneBar hα hβ hFI hfin hN := by
  have h : HeckeInputsOneAlong L M ℓ := heckeInputsOneAlong_intro h0 hα hβ hFI hfin hN
  rw [heckeOperatorOneAlong, dif_pos h]


public theorem heckeOperatorOneAlong_of_not (h : ¬ HeckeInputsOneAlong L M ℓ) :
    heckeOperatorOneAlong L M ℓ = 0 := by
  rw [heckeOperatorOneAlong, dif_neg h]

end Total

section ModularInstance

variable (M ℓ : ℕ) [NeZero ℓ]

example :
    x1FunctionFieldBar M →ₐ[AlgebraicClosure ℚ]
      laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ M (M * ℓ)) :=
  heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ

example : JOne M →+ JOne M :=
  heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ

end ModularInstance

end ModularCurve

end
