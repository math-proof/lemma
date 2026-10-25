import Mathlib
import Def.ModularCurve_JZeroNeronDataPrime
import Def.ModularCurve_EisensteinIdeal
import Structure.ModularCurve_FppfKummerInterface
import Def.ModularCurve_MazurStepThreeInputs
import Instance.AlgebraicGeometry_FppfSiteCohomology
import Instance.AlgebraicGeometry_FppfCohomologyLES
import Instance.AlgebraicGeometry_FppfKummerProp17
import Def.ModularCurve_JZeroToricTorsion
import Structure.ModularCurve_JZeroNeronPrimaryTorsionSheaf

set_option autoImplicit false

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
