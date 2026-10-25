/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean -/


import Lemma.Nat.NumberField.ExtensionDiscriminantLocalization
import Abbrev.MathlibExtTest.NumberTheory.NumberField.ExtensionDiscriminantLocalization


namespace ConcreteLocalization

theorem S_le_nonZeroDivisors : S ≤ nonZeroDivisors ℤ := by
  intro x hx
  rw [mem_nonZeroDivisors_iff_ne_zero]
  obtain ⟨n, rfl⟩ := hx
  exact pow_ne_zero n (by norm_num)

end ConcreteLocalization
