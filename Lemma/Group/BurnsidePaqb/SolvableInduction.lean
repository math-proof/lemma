import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.BurnsidePaqb.SolvableInduction
open BurnsidePaqb


/--
[eq_prime_pow_mul_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SolvableInduction.lean)
-/
@[path]
private lemma eq_prime_pow_mul_of_dvd_eq
  {G : Type u} [Group G] [Fintype G]
  {p q a b d : ℕ}
-- given
  (hp : p.Prime)
  (hq : q.Prime)
  (hdvd : d ∣ p ^ a * q ^ b) :
-- imply
  ∃ a' b', d = p ^ a' * q ^ b' := by
-- proof
  apply BurnsidePaqb.eq_prime_pow_mul_of_dvd hp hq hdvd

/--
[isSolvable_of_prime_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SolvableInduction.lean)
-/
@[path]
private lemma isSolvable_of_prime_card_eq
  {G : Type u} [Group G] [Fintype G]
  {r : ℕ}
-- given
  (hr : r.Prime)
  (hcard : Fintype.card G = r) :
-- imply
  Group.IsSolvable G := by
-- proof
  apply BurnsidePaqb.isSolvable_of_prime_card r hr hcard

/--
[burnside_paqb_of_simple_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SolvableInduction.lean)
-/
@[path]
private lemma burnside_paqb_of_simple_prime_eq
  {G : Type u} [Group G] [Fintype G]
  {p q a b : ℕ}
-- given
  (C6 : ∀ {H : Type u} [Group H] [Fintype H], IsSimpleGroup H → (∃ g : H, g ≠ 1 ∧ IsPrimePow (conjClass g).card) → ∃ r : ℕ, r.Prime ∧ Fintype.card H = r)
  (hp : Nat.Prime p)
  (hq : Nat.Prime q)
  (hcard : Fintype.card G = p ^ a * q ^ b) :
-- imply
  Group.IsSolvable G := by
-- proof
  apply BurnsidePaqb.burnside_paqb_of_simple_prime C6 p q a b hp hq hcard


-- created on 2026-10-20
