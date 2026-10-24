import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.NumberTheory.NumberField.ExtensionDiscriminantLocalization
open ConcreteLocalization


/--
[S_le_nonZeroDivisors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean)
-/
@[path]
private lemma S_le_nonZeroDivisors_eq :
-- imply
  S ≤ nonZeroDivisors ℤ := by
-- proof
  apply ConcreteLocalization.S_le_nonZeroDivisors


-- created on 2026-10-23
