import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[pow_pow_modEq_one_of_modEq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimePowerLifting.lean)
-/
@[path]
lemma pow_pow_modEq_one_of_modEq_one
  {p n a : ℕ}
-- given
  (h : Nat.ModEq p a 1) :
-- imply
  Nat.ModEq (p ^ (n + 1)) (a ^ (p ^ n)) 1 := by
-- proof
  rw [Nat.modEq_iff_dvd] at h ⊢
  simpa using dvd_sub_pow_of_dvd_sub h n
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[prime_power_lifting_modEq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimePowerLifting.lean)
-/
@[path]
lemma prime_power_lifting_modEq_one
  {p n a : ℕ}
-- given
  (hp : Nat.Prime p)
  (hn : 0 < n)
  (ha : 0 < a)
  (h : Nat.ModEq p a 1) :
-- imply
  Nat.ModEq (p ^ (n + 1)) (a ^ (p ^ n)) 1 := by
-- proof
  exact pow_pow_modEq_one_of_modEq_one p n a h

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
