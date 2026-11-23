import Def.AlgebraicCurve_Correspondence
import Def.ModularCurve_X1

set_option autoImplicit false

noncomputable section

open IsDedekindDomain

namespace ModularCurve

open AlgebraicCurve IntermediateField HahnSeries


variable {L : Type*} [Field L] [Algebra ℚ L]
variable (M ℓ : ℕ) [NeZero ℓ]

section DegeneracyMaps

variable (L) in

def heckeAlphaOneBar :
    laurentBaseChange L (x1FunctionField M) →ₐ[L]
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)) :=
  IntermediateField.inclusion (laurentBaseChange_mono₁ L (x1FunctionFieldC_le_x1x0 ℚ M (M * ℓ)))

omit [NeZero ℓ] in
def HeckeBetaOneDefined : Prop :=
  ∀ y ∈ x1FunctionField M, qExpand ℚ ℓ y ∈ x1x0FunctionFieldC ℚ M (M * ℓ)

variable (L) in

def heckeBetaOneBarRingHomOf (h : HeckeBetaOneDefined M ℓ) :
    laurentBaseChange L (x1FunctionField M) →+*
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)) where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L), qExpand_mem_laurentBaseChange₁ ℓ h x.2⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)

variable (L) in

def heckeBetaOneBarOf (h : HeckeBetaOneDefined M ℓ) :
    laurentBaseChange L (x1FunctionField M) →ₐ[L]
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)) :=
  { heckeBetaOneBarRingHomOf L M ℓ h with
    commutes' := fun a => Subtype.ext <| by
      show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

open Classical in
variable (L) in

def heckeBetaOneBar :
    laurentBaseChange L (x1FunctionField M) →ₐ[L]
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)) :=
  if h : HeckeBetaOneDefined M ℓ then heckeBetaOneBarOf L M ℓ h else heckeAlphaOneBar L M ℓ

end DegeneracyMaps

section HeckePic0OneBar

variable (L) in

def HeckeAlphaOneBarIntegral : Prop :=
  (heckeAlphaOneBar L M ℓ).toRingHom.IsIntegral

variable (L) in

def HeckeBetaOneBarIntegral : Prop :=
  (heckeBetaOneBar L M ℓ).toRingHom.IsIntegral

variable {M ℓ}
variable (hα : HeckeAlphaOneBarIntegral L M ℓ) (hβ : HeckeBetaOneBarIntegral L M ℓ)
variable [HasPrincipalDivisors L (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)))]

def heckeDivOneBar :
    Divisor L (laurentBaseChange L (x1FunctionField M)) →+
      Divisor L (laurentBaseChange L (x1FunctionField M)) :=
  Divisor.correspondence (heckeBetaOneBar L M ℓ) (heckeAlphaOneBar L M ℓ) hβ hα

def heckePic0OneBar
    (hFI : FundamentalIdentityAlong L (heckeBetaOneBar L M ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaOneBar L M ℓ))
    (hN : NormFormulaAlong L (heckeAlphaOneBar L M ℓ) hfin) :
    Pic0 L (laurentBaseChange L (x1FunctionField M)) →+
      Pic0 L (laurentBaseChange L (x1FunctionField M)) :=
  Pic0.correspondence (heckeBetaOneBar L M ℓ) (heckeAlphaOneBar L M ℓ) hβ hα hFI hfin hN

def heckeDivOneBarTranspose :
    Divisor L (laurentBaseChange L (x1FunctionField M)) →+
      Divisor L (laurentBaseChange L (x1FunctionField M)) :=
  Divisor.correspondence (heckeAlphaOneBar L M ℓ) (heckeBetaOneBar L M ℓ) hα hβ

def heckePic0OneBarTranspose
    (hFI : FundamentalIdentityAlong L (heckeAlphaOneBar L M ℓ) hα)
    (hfin : FiniteAlong L (heckeBetaOneBar L M ℓ))
    (hN : NormFormulaAlong L (heckeBetaOneBar L M ℓ) hfin) :
    Pic0 L (laurentBaseChange L (x1FunctionField M)) →+
      Pic0 L (laurentBaseChange L (x1FunctionField M)) :=
  Pic0.correspondence (heckeAlphaOneBar L M ℓ) (heckeBetaOneBar L M ℓ) hα hβ hFI hfin hN

end HeckePic0OneBar

section Total

variable (L)

def HeckeInputsOneAlong : Prop :=
  ∃ (_ : HeckeBetaOneDefined M ℓ) (_ : HeckeAlphaOneBarIntegral L M ℓ) (hβ : HeckeBetaOneBarIntegral L M ℓ)
    (_ : HasPrincipalDivisors L (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))))
    (hfin : FiniteAlong L (heckeAlphaOneBar L M ℓ)),
    FundamentalIdentityAlong L (heckeBetaOneBar L M ℓ) hβ ∧
      NormFormulaAlong L (heckeAlphaOneBar L M ℓ) hfin

open Classical in

def heckeOperatorOneAlong :
    Pic0 L (laurentBaseChange L (x1FunctionField M)) →+
      Pic0 L (laurentBaseChange L (x1FunctionField M)) :=
  if h : HeckeInputsOneAlong L M ℓ then
    haveI := h.snd.snd.snd.fst
    heckePic0OneBar h.snd.fst h.snd.snd.fst h.snd.snd.snd.snd.snd.1 h.snd.snd.snd.snd.fst
      h.snd.snd.snd.snd.snd.2
  else 0

variable {L M ℓ}

end Total


end ModularCurve

end
