import Mathlib
import Class.AlgebraicCurve_DivisorPushPull
import Lemma.AlgebraicCurve.AdelicIndex
import Structure.AlgebraicCurve_PoleDivisorPackage
import Abbrev.AlgebraicCurve_PoleDivisorPackage

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve


def HasPoleDivisorPackage (K F : Type*) [Field K] [Field F] [Algebra K F] : Prop :=
  Nonempty (PoleDivisorPackage K F)

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]


namespace TranscendenceTower

variable (T : TranscendenceTower K E F)


def RegularOutside (A : Type*) [CommRing A] [Algebra A E] (T : TranscendenceTower K E F) : Prop :=
  ∀ u : Place K E, u ≠ T.v → ∀ a : A, algebraMap A E a ∈ u.toValuationSubring

end TranscendenceTower


variable (K E F) in

def HasIntegralBasisInLSpace [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
    (T : TranscendenceTower K E F) : Prop :=
  Nonempty (IntegralBasisInLSpace T)

variable (K E F) in

def HasIntegralBasisRegularOutside [Algebra.IsSeparable E F] (T : TranscendenceTower K E F) : Prop :=
  ∃ u : Fin (Module.finrank E F) → F, LinearIndependent E u ∧
    ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)

variable (K E F) in

def HasRegularFractionSubring (T : TranscendenceTower K E F) : Prop :=
  ∃ (A : Subalgebra K E), IsFractionRing A E ∧
    ∀ u : Place K E, u ≠ T.v → ∀ a ∈ A, a ∈ u.toValuationSubring

end AlgebraicCurve

end
