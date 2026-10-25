/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean -/


import Lemma.Nat.NumberField.ExtensionDiscriminantLocalization
import Theorem.MathlibExtTest.NumberTheory.NumberField.ExtensionDiscriminantLocalization


namespace ConcreteLocalization

abbrev S : Submonoid ℤ := Submonoid.powers 2

abbrev SA := Localization S

end ConcreteLocalization
