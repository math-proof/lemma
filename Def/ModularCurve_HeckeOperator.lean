module

public import Def.AlgebraicCurve_Correspondence
public import Theorem.LaurentSeries.ArithmeticGalois

@[expose] public section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain

namespace ModularCurve

open AlgebraicCurve IntermediateField HahnSeries


variable {L : Type*} [Field L] [Algebra ℚ L]
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

section DegeneracyMapsBar

variable (L) in

def heckeAlphaBar :
    laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) :=
  IntermediateField.inclusion
    (laurentBaseChange_mono' L (full_degeneracy_le (dvd_mul_right N ℓ)))

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
variable (L) in

def heckeBetaBar :
    laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) :=
  { heckeBetaBarRingHom L N ℓ with
    commutes' := fun a => Subtype.ext <| by
      show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

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

end ModularInstance

end ModularCurve

end
