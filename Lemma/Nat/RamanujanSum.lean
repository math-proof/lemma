import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RamanujanSum
open MetaMathlibExt


/--
[ramanujanSum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamanujanSum.lean)
-/
@[path]
private lemma ramanujanSum_zero_eq
  {n : ℕ} [NeZero n] :
-- imply
  ramanujanSum n 0 = Nat.totient n := by
-- proof
  apply MetaMathlibExt.ramanujanSum_zero n

/--
[ramanujanSum_modulus_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamanujanSum.lean)
-/
@[path]
private lemma ramanujanSum_modulus_one_eq
  {t : ℤ} :
-- imply
  ramanujanSum 1 t = 1 := by
-- proof
  apply MetaMathlibExt.ramanujanSum_modulus_one t

/--
[ramanujanSum_add_mul_modulus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamanujanSum.lean)
-/
@[path]
private lemma ramanujanSum_add_mul_modulus_eq
  {n : ℕ} [NeZero n]
  {t k : ℤ} :
-- imply
  ramanujanSum n (t + k * n) = ramanujanSum n t := by
-- proof
  apply MetaMathlibExt.ramanujanSum_add_mul_modulus n t k


-- created on 2026-10-20
