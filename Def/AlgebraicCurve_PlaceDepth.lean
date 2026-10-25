import Mathlib
import Lemma.AlgebraicCurve.GluedPic0
import Def.AlgebraicCurve_PlaceEvaluation
import Lemma.AlgebraicCurve.GluedPic0Functoriality

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

namespace Place

variable {L F : Type*} [Field L] [Field F] [Algebra L F]
variable (A : ValuationSubring L) (V : Place L F)

def HasValuation (f : F) (γ : A.ValueGroup) : Prop :=
  ∃ a : L, V.HasValue f a ∧ A.valuation a = γ


def HasDepth (f : F) (ϖ : L) (n : ℕ) : Prop :=
  V.HasValuation A f (A.valuation ϖ ^ n)


def DepthBetween (f : F) (ϖ : L) (m n : ℕ) : Prop :=
  ∃ a : L, V.HasValue f a ∧ A.valuation ϖ ^ n < A.valuation a ∧ A.valuation a < A.valuation ϖ ^ m


end Place

end AlgebraicCurve

namespace ValuationSubring

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

def IsAtDepth (O : ValuationSubring F) (f : F) (ϖ : L) (n : ℕ) : Prop :=
  O.valuation f = O.valuation (algebraMap L F ϖ) ^ n


end ValuationSubring

end
