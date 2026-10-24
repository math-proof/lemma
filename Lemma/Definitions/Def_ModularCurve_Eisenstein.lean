import Lemma.Definitions.Def_HeckeGalois_EichlerShimura
import Lemma.Definitions.Def_ModularCurve_HeckeOperator
import Lemma.Definitions.Def_ModularCurve_CuspidalClass

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

def EisensteinQuotientInvariantsFiniteAt (p : ℕ) [NeZero p]
    (inst : Module HeckeAlg (JZero p)) : Prop :=
  letI := inst
  EisensteinQuotientInvariantsFinite
    (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero p) (eisensteinIdeal p)

def SpecializationSlot (p q : ℕ) [NeZero p] (inst : Module HeckeAlg (JZero p)) : Prop :=
  letI := inst
  SpecializationExists (K := ℚ) (L := AlgebraicClosure ℚ) p q (JZero p)

def HeckeKillsCuspidalClass (p ℓ : ℕ) [NeZero p] [NeZero ℓ]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) p ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * ℓ))]
    (hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) hβ)
    (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) p ℓ))
    (hN : NormFormulaAlong (AlgebraicClosure ℚ)
      (heckeAlphaBar (AlgebraicClosure ℚ) p ℓ) hfin) : Prop :=
  heckePic0Bar hα hβ hFI hfin hN (cuspidalClass p) - (1 + ℓ : ℤ) • cuspidalClass p = 0

def EisensteinKernelKillsCuspidalClass (p : ℕ) [NeZero p]
    (inst : Module HeckeAlg (JZero p)) : Prop :=
  letI := inst
  ∀ t ∈ eisensteinKernel (JZero p) (eisensteinIdeal p), t • cuspidalClass p = 0

end ModularCurve
