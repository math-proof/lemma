import Mathlib
import Structure.ModularCurve_JZeroNeronDataPrime
import Def.ModularCurve_EisensteinIdeal
import Structure.ModularCurve_FppfKummerInterface
import Abbrev.ModularCurve_MazurStepThreeInputs
import Instance.AlgebraicGeometry_FppfSiteCohomology
import Instance.AlgebraicGeometry_FppfCohomologyLES
import Instance.AlgebraicGeometry_FppfKummerProp17
import Def.ModularCurve_JZeroToricTorsion

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring Opposite

abbrev eisensteinPrimaryTorsionBar (p q m : ℕ) [NeZero p] : AddSubgroup (JZero p) :=
  letI := heckeModuleBar p
  (AddMonoidHom.ker ((q ^ m : ℤ) • AddMonoidHom.id (JZero p))) ⊓
    ⨆ k : ℕ, (Submodule.torsionBySet HeckeAlg (JZero p)
      (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)).toAddSubgroup

abbrev toricEisensteinPrimaryPart (p q : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (_hA : A.LiesOverPrime p) (m : ℕ) :
    AddSubgroup (JZero p) :=
  jZeroToricTorsion p A (q ^ m) ⊓ eisensteinPrimaryTorsionBar p q m

abbrev eisensteinQuotientRationalLocalized (p q : ℕ) [NeZero p] [Fact q.Prime] : Type :=
  letI := heckeModuleBar p
  LocalizedModule (eisensteinMaximalIdeal p q).primeCompl
    ↥(Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p)))


end ModularCurve
end
