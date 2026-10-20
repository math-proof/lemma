import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Digits.SutcliffeReverseMultiple
open MetaMathlibExt


/--
[sutcliffe_two_to_three_digit_reverse_multiple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/SutcliffeReverseMultiple.lean)
-/
@[path]
private lemma sutcliffe_two_to_three_digit_reverse_multiple_eq
  {g k a b : ℕ}
-- given
  (hk : 2 ≤ k)
  (hkg : k < g)
  (ha : a ≠ 0)
  (hag : a < g)
  (hbg : b < g)
  (hreverse : k * (a * g + b) = b * g + a) :
-- imply
  a + b < g ∧
      k * (a * g ^ 2 + (a + b) * g + b) =
        b * g ^ 2 + (a + b) * g + a := by
-- proof
  apply MetaMathlibExt.sutcliffe_two_to_three_digit_reverse_multiple g k a b hk hkg ha hag hbg hreverse


-- created on 2026-10-20
