import Mathlib
import sympy.Basic
import sympy.atlas.Data.Nat.Digits.Reverse
open Nat


/--
[reverseDigits_base_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/Digits/Reverse.lean)
-/
@[path]
private lemma reverseDigits_base_zero_eq
  {n : ℕ} :
-- imply
  reverseDigits 0 n = n := by
-- proof
  apply Nat.reverseDigits_base_zero n

/--
[reverseDigits_base_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/Digits/Reverse.lean)
-/
@[path]
private lemma reverseDigits_base_one_eq
  {n : ℕ} :
-- imply
  reverseDigits 1 n = n := by
-- proof
  apply Nat.reverseDigits_base_one n


-- created on 2026-10-20
