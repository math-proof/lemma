-- Carved from Lemma/Definitions/Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf.lean: instance decls only.
-- Carved: selected defs -> Def.ModularCurve_JZeroNeronPrimaryTorsionSheaf; leftover decls remain here
import Mathlib
import Def.ModularCurve_JZeroNeronDataPrime
import Lemma.ModularCurve.EisensteinIdeal
import Structure.ModularCurve_FppfKummerInterface
import Def.ModularCurve_MazurStepThreeInputs
import Instance.AlgebraicGeometry_FppfSiteCohomology
import Instance.AlgebraicGeometry_FppfCohomologyLES
import Instance.AlgebraicGeometry_FppfKummerProp17
import Lemma.ModularCurve.JZeroToricTorsion
import Structure.ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Def.ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Theorem.DefinitionsStaging.ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Abbrev.ModularCurve_JZeroNeronPrimaryTorsionSheaf

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring Opposite

instance eisensteinMaximalIdeal.isPrime (N q : ℕ) [Fact q.Prime] :
    (eisensteinMaximalIdeal N q).IsPrime := by
  have hq : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  haveI : (Ideal.span {(q : ℤ)}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  exact Ideal.IsPrime.comap _


end ModularCurve

end
