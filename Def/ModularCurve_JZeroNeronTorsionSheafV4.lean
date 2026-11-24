module
public import Mathlib
public import Def.ModularCurve_JZeroNeronDataPrime
public import Theorem.Ideal.EisensteinIdeal
public import Structure.ModularCurve_FppfKummerInterface
public import Def.ModularCurve_MazurStepThreeInputs
public import Instance.AlgebraicGeometry_FppfSiteCohomology
public import Lemma.Scheme.FppfCohomologyLES
public import Lemma.Scheme.FppfKummerProp17
public import Theorem.ValuationSubring.JZeroToricTorsion
public import Abbrev.ModularCurve_JZeroNeronTorsionSheafV4
public import Structure.ModularCurve_JZeroNeronTorsionSheafV4
set_option autoImplicit false


public section

noncomputable section

namespace ModularCurve

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring Opposite


def HasJZeroNeronTorsionSheaf (p q : ℕ) [Fact p.Prime] [Fact q.Prime] : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
    Nonempty (JZeroNeronTorsionSheaf p q A hA)

section Falseprobe

end Falseprobe

end ModularCurve

end
