/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimePowerLifting.lean -/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.Basic

namespace MetaMathlibExt

/-- Lifting a congruence to one: if `a ≡ 1 [MOD p]` for any natural modulus `p` (not
necessarily prime), then `a ^ (p ^ n) ≡ 1 [MOD p ^ (n + 1)]` for every `n`. It is the `Nat.ModEq`
form of `dvd_sub_pow_of_dvd_sub`; `prime_power_lifting_modEq_one` is the source-shaped form. -/
theorem pow_pow_modEq_one_of_modEq_one (p n a : ℕ) (h : Nat.ModEq p a 1) :
    Nat.ModEq (p ^ (n + 1)) (a ^ (p ^ n)) 1 := by
  rw [Nat.modEq_iff_dvd] at h ⊢
  simpa using dvd_sub_pow_of_dvd_sub h n

set_option linter.unusedVariables false in
/--
Prime-power lifting for a natural number congruent to one modulo a prime.

Source: Hacène Belbachir and Celia Salhi, "The Generalized Bi-Periodic
Fibonacci Sequence Modulo m," Journal of Integer Sequences 24 (2021),
Article 21.9.4, Theorem (label th4), lines 340–341,
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Salhi/salhi4.tex>.
It follows from `pow_pow_modEq_one_of_modEq_one`; the hypotheses `hp`, `hn` and `ha` are
unused and keep the source's shape.
Proves `Wanted` entry `prime_power_lifting_modEq_one`.
-/
theorem prime_power_lifting_modEq_one
    (p n a : ℕ) (hp : Nat.Prime p) (hn : 0 < n) (ha : 0 < a)
    (h : Nat.ModEq p a 1) :
    Nat.ModEq (p ^ (n + 1)) (a ^ (p ^ n)) 1 := by
  exact pow_pow_modEq_one_of_modEq_one p n a h

end MetaMathlibExt
