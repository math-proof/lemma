module
public import Abbrev.NumberTheory.NumberField.Idele.Part2
public import Theorem.Nat.NumberField.Idele
public import Theorem.MathlibExtTest.NumberTheory.NumberField.Idele


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Idele.lean -/
/-
Author: @toskua, Avocado
-/
noncomputable section

open NumberField IsDedekindDomain

section TestIntRational

def testAdeleUnitsToIdele : (AdeleRing ℤ ℚ)ˣ →* TopologicalIdeleGroup ℤ ℚ :=
  (TopologicalIdeleGroup.unitsEquiv ℤ ℚ).toMonoidHom

def testIdeleToAdeleUnits : TopologicalIdeleGroup ℤ ℚ →* (AdeleRing ℤ ℚ)ˣ :=
  (TopologicalIdeleGroup.unitsEquiv ℤ ℚ).symm.toMonoidHom

end TestIntRational
end
