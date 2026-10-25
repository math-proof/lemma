import Lemma.AlgebraicCurve.Correspondence
import Lemma.ModularCurve.ArithmeticGalois

set_option autoImplicit false

noncomputable section

open IsDedekindDomain

namespace ModularCurve

open AlgebraicCurve IntermediateField HahnSeries

section PrivateSupply

variable {L : Type*} [Field L] [Algebra ℚ L]

private theorem coeffMap_qExpand' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

private theorem coeffEmb_qExpand' (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) :=
  coeffMap_qExpand' _ n x

variable (L) in
private theorem laurentBaseChange_mono' {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

private theorem qExpand_mem_laurentBaseChange' {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ)
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
      · rw [← coeffEmb_qExpand']
        exact coeffEmb_mem_laurentBaseChange L (hF z hz)
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

end PrivateSupply

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

section DegeneracyMapsBar

variable (L) in

def heckeAlphaBar :
    laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) :=
  IntermediateField.inclusion
    (laurentBaseChange_mono' L (full_degeneracy_le (dvd_mul_right N ℓ)))

@[simp]
theorem coe_heckeAlphaBar (x : laurentBaseChange L (modularFunctionFieldFull N)) :
    (heckeAlphaBar L N ℓ x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

variable (L) in

def heckeBetaBarRingHom :
    laurentBaseChange L (modularFunctionFieldFull N) →+*
      laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L),
    qExpand_mem_laurentBaseChange' ℓ
      (fun y hy => full_degeneracy_map_le (N := N) ℓ ⟨y, hy, rfl⟩) x.2⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)

omit [NeZero N] in
@[simp]
theorem coe_heckeBetaBarRingHom (x : laurentBaseChange L (modularFunctionFieldFull N)) :
    (heckeBetaBarRingHom L N ℓ x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
  rfl

variable (L) in

def heckeBetaBar :
    laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) :=
  { heckeBetaBarRingHom L N ℓ with
    commutes' := fun a => Subtype.ext <| by
      show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

theorem heckeAlphaBar_eq_inclusion
    (h : laurentBaseChange L (modularFunctionFieldFull N)
      ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :
    heckeAlphaBar L N ℓ = IntermediateField.inclusion h :=
  rfl

omit [NeZero N] in
@[simp]
theorem coe_heckeBetaBar (x : laurentBaseChange L (modularFunctionFieldFull N)) :
    (heckeBetaBar L N ℓ x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
  rfl

end DegeneracyMapsBar

section HeckePic0Bar

variable (L) in

def HeckeAlphaBarIntegral : Prop :=
  (heckeAlphaBar L N ℓ).toRingHom.IsIntegral

variable (L) in

def HeckeBetaBarIntegral : Prop :=
  (heckeBetaBar L N ℓ).toRingHom.IsIntegral

variable {N ℓ}
variable (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
variable [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]

def heckeDivBar :
    Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) →+
      Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) :=
  Divisor.correspondence (heckeBetaBar L N ℓ) (heckeAlphaBar L N ℓ) hβ hα

def heckePic0Bar
    (hFI : FundamentalIdentityAlong L (heckeBetaBar L N ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaBar L N ℓ))
    (hN : NormFormulaAlong L (heckeAlphaBar L N ℓ) hfin) :
    Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) →+
      Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) :=
  Pic0.correspondence (heckeBetaBar L N ℓ) (heckeAlphaBar L N ℓ) hβ hα hFI hfin hN

end HeckePic0Bar

section Transpose

variable {N ℓ}
variable (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
variable [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]

def heckeDivBarTranspose :
    Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) →+
      Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) :=
  Divisor.correspondence (heckeAlphaBar L N ℓ) (heckeBetaBar L N ℓ) hα hβ

def heckePic0BarTranspose
    (hFI : FundamentalIdentityAlong L (heckeAlphaBar L N ℓ) hα)
    (hfin : FiniteAlong L (heckeBetaBar L N ℓ))
    (hN : NormFormulaAlong L (heckeBetaBar L N ℓ) hfin) :
    Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) →+
      Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) :=
  Pic0.correspondence (heckeAlphaBar L N ℓ) (heckeBetaBar L N ℓ) hα hβ hFI hfin hN

end Transpose

section ModularInstance

example :
    (modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ] (modularFunctionFieldBar (N * ℓ)) :=
  heckeAlphaBar (AlgebraicClosure ℚ) N ℓ

example (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))]
    (hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ)
    (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ))
    (hN : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hfin) :
    JZero N →+ JZero N :=
  heckePic0Bar hα hβ hFI hfin hN

end ModularInstance

end ModularCurve

end
