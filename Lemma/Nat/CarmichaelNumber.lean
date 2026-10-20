import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.CarmichaelNumber


/--
[Nat.isCarmichaelNumber_iff_zmod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CarmichaelNumber.lean)
-/
@[path]
private lemma Nat_isCarmichaelNumber_iff_zmod_eq
  {n : ℕ} :
-- imply
  Nat.IsCarmichaelNumber n ↔
    1 < n ∧ ¬n.Prime ∧ ∀ x : ZMod n, x ^ n = x := by
-- proof
  apply Nat.isCarmichaelNumber_iff_zmod n

/--
[Nat.isCarmichaelNumber_iff_korselt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CarmichaelNumber.lean)
-/
@[path]
private lemma Nat_isCarmichaelNumber_iff_korselt_eq
  {n : ℕ}
-- given
  (hn : 1 < n) :
-- imply
  Nat.IsCarmichaelNumber n ↔
    Squarefree n ∧
    (∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)) ∧ ¬n.Prime := by
-- proof
  apply Nat.isCarmichaelNumber_iff_korselt n hn


-- created on 2026-10-20
