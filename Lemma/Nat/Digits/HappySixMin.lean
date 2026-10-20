import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Digits.HappySixMin
open MetaMathlibExt


/--
[happy_six_min](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/HappySixMin.lean)
-/
@[path]
private lemma happy_six_min_eq
  :
-- imply
  (∀ j : ℕ, j < 6 →
    ∃ k : ℕ, ∃ f : ℕ → ℕ,
    f 0 = (7899999999999959999999996 + j) ∧
    f k = 1 ∧
    ∀ i : ℕ, i < k →
    f (i + 1) = (((Nat.digits 10 (f i)).map (fun d => d ^ 2)).sum)) ∧
    ∀ m : ℕ,
    (∀ j : ℕ, j < 6 →
    ∃ k : ℕ, ∃ f : ℕ → ℕ,
    f 0 = (m + j) ∧
    f k = 1 ∧
    ∀ i : ℕ, i < k →
    f (i + 1) = (((Nat.digits 10 (f i)).map (fun d => d ^ 2)).sum)) →
    7899999999999959999999996 ≤ m := by
-- proof
  apply MetaMathlibExt.happy_six_min


-- created on 2026-10-20
