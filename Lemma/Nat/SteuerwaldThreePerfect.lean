import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SteuerwaldThreePerfect
open MetaMathlibExt


/--
[pillai_equations_two_pow_three_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SteuerwaldThreePerfect.lean)
-/
@[path]
private lemma pillai_equations_two_pow_three_pow_eq
  :
-- imply
  (∀ a b : ℕ, (2 : ℤ) ^ a - 3 ^ b = -1 ↔
    (a = 1 ∧ b = 1) ∨ (a = 3 ∧ b = 2)) ∧
    (∀ a b c : ℕ, (2 : ℤ) ^ a - 3 ^ b = 2 ^ c - 1 ↔
    (a = 2 ∧ b = 1 ∧ c = 1) ∨ (a = 4 ∧ b = 2 ∧ c = 3) ∨
    (b = 0 ∧ c = a)) := by
-- proof
  apply MetaMathlibExt.pillai_equations_two_pow_three_pow

/--
[steuerwald_three_perfect_exponents](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SteuerwaldThreePerfect.lean)
-/
@[path]
private lemma steuerwald_three_perfect_exponents_eq
  {N a b m : ℕ}
-- given
  (hperfect : ArithmeticFunction.sigma 1 N = 3 * N)
  (hform : N = 2 ^ a * 3 ^ b * m)
  (ha : 1 ≤ a)
  (hb : 1 ≤ b)
  (hcoprime : Nat.Coprime 6 m) :
-- imply
  (a = 1 ∧ b ≠ 1) ∨ (a ≠ 1 ∧ b = 1) := by
-- proof
  apply MetaMathlibExt.steuerwald_three_perfect_exponents N a b m hperfect hform ha hb hcoprime


-- created on 2026-10-20
