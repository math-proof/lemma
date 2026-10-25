/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean -/


import Lemma.Nat.NumberField.ExtensionDiscriminantLocalization
import Instance.MathlibExtTest.NumberTheory.NumberField.ExtensionDiscriminantLocalization


namespace ConcreteLocalization

noncomputable abbrev q : SA :=
  IsLocalization.mk' (M := S) SA (1 : ℤ) (⟨2, Submonoid.mem_powers 2⟩ : S)

end ConcreteLocalization
