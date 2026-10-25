import Mathlib
import Def.ModularCurve_JZeroNeronDataPrime
import Lemma.ModularCurve.EisensteinIdeal
import Structure.ModularCurve_FppfKummerInterface
import Def.ModularCurve_MazurStepThreeInputs
import Instance.AlgebraicGeometry_FppfSiteCohomology
import Lemma.AlgebraicGeometry.FppfCohomologyLES
import Lemma.AlgebraicGeometry.FppfKummerProp17
import Lemma.ModularCurve.JZeroToricTorsion
import Abbrev.ModularCurve_JZeroNeronTorsionSheafV4
import Structure.ModularCurve_JZeroNeronTorsionSheafV4

set_option autoImplicit false

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
