import Lemma.ModularCurve.HeckeOperator

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

end ModularCurve

end
