import Lemma.Definitions.Def_ModularCurve_HeckeOperator

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

def HeckeInputsAlong : Prop :=
  ∃ (_ : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
    (_ : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))))
    (hfin : FiniteAlong L (heckeAlphaBar L N ℓ)),
    FundamentalIdentityAlong L (heckeBetaBar L N ℓ) hβ ∧
      NormFormulaAlong L (heckeAlphaBar L N ℓ) hfin

open Classical in

def heckeOperatorAlong :
    Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) →+
      Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) :=
  if h : HeckeInputsAlong L N ℓ then
    haveI := h.snd.snd.fst
    heckePic0Bar h.fst h.snd.fst h.snd.snd.snd.snd.1 h.snd.snd.snd.fst h.snd.snd.snd.snd.2
  else 0

variable {L N ℓ}

theorem heckeInputsAlong_intro (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
    [hP : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]
    (hFI : FundamentalIdentityAlong L (heckeBetaBar L N ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaBar L N ℓ))
    (hN : NormFormulaAlong L (heckeAlphaBar L N ℓ) hfin) : HeckeInputsAlong L N ℓ :=
  ⟨hα, hβ, hP, hfin, hFI, hN⟩

theorem heckeOperatorAlong_eq (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]
    (hFI : FundamentalIdentityAlong L (heckeBetaBar L N ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaBar L N ℓ))
    (hN : NormFormulaAlong L (heckeAlphaBar L N ℓ) hfin) :
    heckeOperatorAlong L N ℓ = heckePic0Bar hα hβ hFI hfin hN := by
  have h : HeckeInputsAlong L N ℓ := heckeInputsAlong_intro hα hβ hFI hfin hN
  rw [heckeOperatorAlong, dif_pos h]

theorem heckeOperatorAlong_of_not (h : ¬ HeckeInputsAlong L N ℓ) :
    heckeOperatorAlong L N ℓ = 0 := by
  rw [heckeOperatorAlong, dif_neg h]

end ModularCurve

end
