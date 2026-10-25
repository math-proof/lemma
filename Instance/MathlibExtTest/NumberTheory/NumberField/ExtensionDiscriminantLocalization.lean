/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean -/


import Lemma.Nat.NumberField.ExtensionDiscriminantLocalization
import Theorem.MathlibExtTest.NumberTheory.NumberField.ExtensionDiscriminantLocalization.Part2


namespace ConcreteLocalization

noncomputable local instance : Algebra SA (FractionRing ℤ) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe SA (FractionRing ℤ) S
    (nonZeroDivisors ℤ) S_le_nonZeroDivisors

end ConcreteLocalization
