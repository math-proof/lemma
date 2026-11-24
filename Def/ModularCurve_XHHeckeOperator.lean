module
public import Def.AlgebraicCurve_Correspondence
public import Abbrev.ModularCurve_XH
set_option autoImplicit false


public section

noncomputable section

open IsDedekindDomain

namespace ModularCurve

open AlgebraicCurve IntermediateField HahnSeries


variable {L : Type*} [Field L] [Algebra ℚ L]
variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

section DegeneracyMaps

variable (L) in

def heckeAlphaHBar :
    laurentBaseChange L (xHFunctionField M H) →ₐ[L]
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)) :=
  IntermediateField.inclusion (laurentBaseChange_monoH L (xHFunctionFieldC_le_top ℚ M H (M * ℓ)))

omit [NeZero ℓ] in
def HeckeBetaHDefined : Prop :=
  ∀ y ∈ xHFunctionField M H, qExpand ℚ ℓ y ∈ xHTopFunctionFieldC ℚ M H (M * ℓ)

variable (L) in

def heckeBetaHBarRingHomOf (h : HeckeBetaHDefined M H ℓ) :
    laurentBaseChange L (xHFunctionField M H) →+*
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)) where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L), qExpand_mem_laurentBaseChangeH ℓ h x.2⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)

variable (L) in

def heckeBetaHBarOf (h : HeckeBetaHDefined M H ℓ) :
    laurentBaseChange L (xHFunctionField M H) →ₐ[L]
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)) :=
  { heckeBetaHBarRingHomOf L M H ℓ h with
    commutes' := fun a => Subtype.ext <| by
      show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

open Classical in
variable (L) in

def heckeBetaHBar :
    laurentBaseChange L (xHFunctionField M H) →ₐ[L]
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)) :=
  if h : HeckeBetaHDefined M H ℓ then heckeBetaHBarOf L M H ℓ h else heckeAlphaHBar L M H ℓ

end DegeneracyMaps

section HeckePic0HBar

variable (L) in

def HeckeAlphaHBarIntegral : Prop :=
  (heckeAlphaHBar L M H ℓ).toRingHom.IsIntegral

variable (L) in

def HeckeBetaHBarIntegral : Prop :=
  (heckeBetaHBar L M H ℓ).toRingHom.IsIntegral

variable {M H ℓ}
variable (hα : HeckeAlphaHBarIntegral L M H ℓ) (hβ : HeckeBetaHBarIntegral L M H ℓ)
variable [HasPrincipalDivisors L (laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)))]

def heckeDivHBar :
    Divisor L (laurentBaseChange L (xHFunctionField M H)) →+
      Divisor L (laurentBaseChange L (xHFunctionField M H)) :=
  Divisor.correspondence (heckeBetaHBar L M H ℓ) (heckeAlphaHBar L M H ℓ) hβ hα

def heckePic0HBar
    (hFI : FundamentalIdentityAlong L (heckeBetaHBar L M H ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaHBar L M H ℓ))
    (hN : NormFormulaAlong L (heckeAlphaHBar L M H ℓ) hfin) :
    Pic0 L (laurentBaseChange L (xHFunctionField M H)) →+
      Pic0 L (laurentBaseChange L (xHFunctionField M H)) :=
  Pic0.correspondence (heckeBetaHBar L M H ℓ) (heckeAlphaHBar L M H ℓ) hβ hα hFI hfin hN

def heckeDivHBarTranspose :
    Divisor L (laurentBaseChange L (xHFunctionField M H)) →+
      Divisor L (laurentBaseChange L (xHFunctionField M H)) :=
  Divisor.correspondence (heckeAlphaHBar L M H ℓ) (heckeBetaHBar L M H ℓ) hα hβ

def heckePic0HBarTranspose
    (hFI : FundamentalIdentityAlong L (heckeAlphaHBar L M H ℓ) hα)
    (hfin : FiniteAlong L (heckeBetaHBar L M H ℓ))
    (hN : NormFormulaAlong L (heckeBetaHBar L M H ℓ) hfin) :
    Pic0 L (laurentBaseChange L (xHFunctionField M H)) →+
      Pic0 L (laurentBaseChange L (xHFunctionField M H)) :=
  Pic0.correspondence (heckeAlphaHBar L M H ℓ) (heckeBetaHBar L M H ℓ) hα hβ hFI hfin hN

end HeckePic0HBar

section Total

variable (L)

def HeckeInputsHAlong : Prop :=
  ∃ (_ : HeckeBetaHDefined M H ℓ) (_ : HeckeAlphaHBarIntegral L M H ℓ) (hβ : HeckeBetaHBarIntegral L M H ℓ)
    (_ : HasPrincipalDivisors L (laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))))
    (hfin : FiniteAlong L (heckeAlphaHBar L M H ℓ)),
    FundamentalIdentityAlong L (heckeBetaHBar L M H ℓ) hβ ∧
      NormFormulaAlong L (heckeAlphaHBar L M H ℓ) hfin

open Classical in

def heckeOperatorHAlong :
    Pic0 L (laurentBaseChange L (xHFunctionField M H)) →+
      Pic0 L (laurentBaseChange L (xHFunctionField M H)) :=
  if h : HeckeInputsHAlong L M H ℓ then
    haveI := h.snd.snd.snd.fst
    heckePic0HBar h.snd.fst h.snd.snd.fst h.snd.snd.snd.snd.snd.1 h.snd.snd.snd.snd.fst
      h.snd.snd.snd.snd.snd.2
  else 0

variable {L M H ℓ}

end Total


end ModularCurve

end
