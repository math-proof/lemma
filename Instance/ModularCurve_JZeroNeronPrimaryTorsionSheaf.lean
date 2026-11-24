module
public import Mathlib
public import Def.ModularCurve_JZeroNeronDataPrime
public import Theorem.Ideal.EisensteinIdeal
public import Structure.ModularCurve_FppfKummerInterface
public import Def.ModularCurve_MazurStepThreeInputs
public import Instance.AlgebraicGeometry_FppfSiteCohomology
public import Instance.AlgebraicGeometry_FppfCohomologyLES
public import Instance.AlgebraicGeometry_FppfKummerProp17
public import Theorem.ValuationSubring.JZeroToricTorsion
public import Structure.ModularCurve_JZeroNeronPrimaryTorsionSheaf
public import Def.ModularCurve_JZeroNeronPrimaryTorsionSheaf
public import Theorem.DefinitionsStaging.ModularCurve_JZeroNeronPrimaryTorsionSheaf
public import Abbrev.ModularCurve_JZeroNeronPrimaryTorsionSheaf
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf.lean: instance decls only.
-- Carved: selected defs -> Def.ModularCurve_JZeroNeronPrimaryTorsionSheaf; leftover decls remain here

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
