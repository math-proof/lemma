import Lemma.ModularCurve.HeckeOperator
import Def.ModularCurve_HeckeOperatorTotal

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]


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
