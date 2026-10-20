import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Digits.KaprekarStructuralClassification
open MetaMathlibExt


/--
[four_digit_kaprekar_structural_classification](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/KaprekarStructuralClassification.lean)
-/
@[path]
private lemma four_digit_kaprekar_structural_classification_eq
  {B : ℕ}
-- given
  (hB : Odd B)
  (hB3 : 3 < B) :
-- imply
  let X_B : Set (ℕ × ℕ) := by
-- proof
  apply MetaMathlibExt.four_digit_kaprekar_structural_classification B hB hB3


-- created on 2026-10-20
