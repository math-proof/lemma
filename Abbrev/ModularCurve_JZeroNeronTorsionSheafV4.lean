module
public import Mathlib
public import Structure.ModularCurve_JZeroNeronDataPrime
public import Def.ModularCurve_EisensteinIdeal
public import Structure.ModularCurve_FppfKummerInterface
public import Abbrev.ModularCurve_MazurStepThreeInputs
public import Instance.AlgebraicGeometry_FppfSiteCohomology
public import Instance.AlgebraicGeometry_FppfCohomologyLES
public import Instance.AlgebraicGeometry_FppfKummerProp17
public import Def.ModularCurve_JZeroToricTorsion
set_option autoImplicit false


public section

noncomputable section

namespace ModularCurve

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring Opposite

abbrev eisensteinTorsionBar (p q m : ℕ) [NeZero p] : AddSubgroup (JZero p) :=
  letI := heckeModuleBar p
  (Submodule.torsionBySet HeckeAlg (JZero p)
    (↑((eisensteinMaximalIdeal p q) ^ m) : Set HeckeAlg)).toAddSubgroup

abbrev toricEisensteinPart (p q : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (_hA : A.LiesOverPrime p) (m : ℕ) :
    AddSubgroup (JZero p) :=
  jZeroToricTorsion p A (q ^ m) ⊓ eisensteinTorsionBar p q m


section Falseprobe

end Falseprobe

end ModularCurve

end
