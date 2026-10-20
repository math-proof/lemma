import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LucasLehmerAcceptableSeed
open MetaMathlibExt


/--
[acceptableSeed_of_jacobi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean)
-/
@[path]
private lemma acceptableSeed_of_jacobi_eq
  {n : ℕ}
  {s₁ : ℤ}
-- given
  (hn_odd : Odd n)
  (hn_ge : 3 ≤ n) :
-- imply
  jacobiSym (s₁ + 2) (mersenne n) = -1 ∧
    jacobiSym (s₁ - 2) (mersenne n) = 1 →
    (Nat.Prime (mersenne n) ↔
    (mersenne n : ℤ) ∣ Nat.iterate (fun x : ℤ => x ^ 2 - 2) (n - 2) s₁) := by
-- proof
  apply MetaMathlibExt.acceptableSeed_of_jacobi n hn_odd hn_ge s₁


-- created on 2026-10-20
