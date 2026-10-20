import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimePowerLifting
open MetaMathlibExt


/--
[pow_pow_modEq_one_of_modEq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimePowerLifting.lean)
-/
@[path]
private lemma pow_pow_modEq_one_of_modEq_one_eq
  {p n a : ℕ}
-- given
  (h : Nat.ModEq p a 1) :
-- imply
  Nat.ModEq (p ^ (n + 1)) (a ^ (p ^ n)) 1 := by
-- proof
  apply MetaMathlibExt.pow_pow_modEq_one_of_modEq_one p n a h

/--
[prime_power_lifting_modEq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimePowerLifting.lean)
-/
@[path]
private lemma prime_power_lifting_modEq_one_eq
  {p n a : ℕ}
-- given
  (hp : Nat.Prime p)
  (hn : 0 < n)
  (ha : 0 < a)
  (h : Nat.ModEq p a 1) :
-- imply
  Nat.ModEq (p ^ (n + 1)) (a ^ (p ^ n)) 1 := by
-- proof
  apply MetaMathlibExt.prime_power_lifting_modEq_one p n a hp hn ha h


-- created on 2026-10-20
