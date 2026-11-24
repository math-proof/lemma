module
public import Theorem.Nat.NumberField.ExtensionDiscriminantLocalization
public import Instance.MathlibExtTest.NumberTheory.NumberField.ExtensionDiscriminantLocalization


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean -/
namespace ConcreteLocalization

noncomputable abbrev q : SA :=
  IsLocalization.mk' (M := S) SA (1 : ℤ) (⟨2, Submonoid.mem_powers 2⟩ : S)

end ConcreteLocalization
