import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RamanujanSum
open MetaMathlibExt


namespace MetaMathlibExt

/--
[ramanujanSum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamanujanSum.lean)
-/
@[path]
lemma ramanujanSum_zero
  {n : ℕ} [NeZero n] :
-- imply
  ramanujanSum n 0 = Nat.totient n := by
-- proof
  simp [ramanujanSum, ZMod.card_units_eq_totient]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanSum_modulus_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamanujanSum.lean)
-/
@[path]
lemma ramanujanSum_modulus_one
  {t : ℤ} :
-- imply
  ramanujanSum 1 t = 1 := by
-- proof
  have ht : (t : ZMod 1) = 0 := Subsingleton.elim _ _
  simp [ramanujanSum, ht]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanSum_add_mul_modulus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamanujanSum.lean)
-/
@[path]
lemma ramanujanSum_add_mul_modulus
  {n : ℕ} [NeZero n]
  {t k : ℤ} :
-- imply
  ramanujanSum n (t + k * n) = ramanujanSum n t := by
-- proof
  simp [ramanujanSum]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
