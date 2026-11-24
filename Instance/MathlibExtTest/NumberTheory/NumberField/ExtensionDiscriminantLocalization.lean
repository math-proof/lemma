module
public import Theorem.Nat.NumberField.ExtensionDiscriminantLocalization
public import Theorem.MathlibExtTest.NumberTheory.NumberField.ExtensionDiscriminantLocalization.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean -/
namespace ConcreteLocalization

noncomputable local instance : Algebra SA (FractionRing ℤ) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe SA (FractionRing ℤ) S
    (nonZeroDivisors ℤ) S_le_nonZeroDivisors

end ConcreteLocalization
