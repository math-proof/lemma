import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Digits.SloaneReverseMultiple
open MetaMathlibExt


/--
[sloane_reverse_multiple_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/SloaneReverseMultiple.lean)
-/
@[path]
private lemma sloane_reverse_multiple_endpoint_eq
  {g k a₀ aLast : ℕ}
  {digits : List ℕ}
-- given
  (hk : 2 ≤ k)
  (hkg : k < g)
  (hdigits : ∀ d ∈ digits, d < g)
  (hunits : digits.head? = some a₀)
  (hleading : digits.getLast? = some aLast)
  (hleading_ne : aLast ≠ 0)
  (hreverse : k * Nat.ofDigits g digits = Nat.ofDigits g digits.reverse)
  (hendpoint_sum : a₀ + aLast = g) :
-- imply
  (k + 1) * aLast = g ∧ aLast = g / (k + 1) ∧ k + 1 ∣ g := by
-- proof
  apply MetaMathlibExt.sloane_reverse_multiple_endpoint g k a₀ aLast digits hk hkg hdigits hunits hleading hleading_ne hreverse hendpoint_sum


-- created on 2026-10-20
