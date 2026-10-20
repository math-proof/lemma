import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Digits.Midy
open MetaMathlibExt


/--
[midy_theorem_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/Midy.lean)
-/
@[path]
private lemma midy_theorem_general_eq
  {p n : ℕ}
-- given
  (hp : Nat.Prime p)
  (hdiv : p ∣ 10 ^ (2 * n) - 1)
  (hnot : ¬p ∣ 10 ^ n - 1) :
-- imply
  Nat.ofDigits 10 (List.take n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) +
    Nat.ofDigits 10 (List.drop n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) =
    10 ^ n - 1 := by
-- proof
  apply MetaMathlibExt.midy_theorem_general hp hdiv hnot

/--
[midy_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/Midy.lean)
-/
@[path]
private lemma midy_theorem_eq
  {p n : ℕ}
-- given
  (hp : Nat.Prime p)
  (h0 : p ≠ 2)
  (h1 : p ≠ 5)
  (hn : 0 < n)
  (hdiv : p ∣ 10 ^ (2 * n) - 1)
  (hmin : ∀ m : ℕ, 0 < m → m < 2 * n → ¬p ∣ 10 ^ m - 1) :
-- imply
  Nat.ofDigits 10 (List.take n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) +
    Nat.ofDigits 10 (List.drop n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) =
    10 ^ n - 1 := by
-- proof
  apply MetaMathlibExt.midy_theorem hp h0 h1 hn hdiv hmin


-- created on 2026-10-20
