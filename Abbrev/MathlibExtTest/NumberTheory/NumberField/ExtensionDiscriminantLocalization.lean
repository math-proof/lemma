module
public import Theorem.Nat.NumberField.ExtensionDiscriminantLocalization
public import Theorem.MathlibExtTest.NumberTheory.NumberField.ExtensionDiscriminantLocalization


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean -/
namespace ConcreteLocalization

abbrev S : Submonoid ℤ := Submonoid.powers 2

abbrev SA := Localization S

end ConcreteLocalization
