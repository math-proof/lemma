module
public import Mathlib
public import Def.ModularCurve_JZeroNeronDataPrime
public import Def.ModularCurve_EisensteinIdeal
public import Structure.ModularCurve_FppfKummerInterface
public import Def.ModularCurve_MazurStepThreeInputs
public import Instance.AlgebraicGeometry_FppfSiteCohomology
public import Instance.AlgebraicGeometry_FppfCohomologyLES
public import Instance.AlgebraicGeometry_FppfKummerProp17
public import Def.ModularCurve_JZeroToricTorsion
public import Structure.ModularCurve_JZeroNeronPrimaryTorsionSheaf
set_option autoImplicit false


public section

noncomputable section

namespace ModularCurve

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring Opposite


def HasJZeroNeronPrimaryTorsionSheaf (p q : ℕ) [Fact p.Prime] [Fact q.Prime] : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
    Nonempty (JZeroNeronPrimaryTorsionSheaf p q A hA)

section Falseprobe

end Falseprobe

end ModularCurve

end
