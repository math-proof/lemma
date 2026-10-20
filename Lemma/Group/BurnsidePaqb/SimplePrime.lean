import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.BurnsidePaqb.SimplePrime
open BurnsidePaqb


/--
[false_of_one_add_prime_mul_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SimplePrime.lean)
-/
@[path]
private lemma false_of_one_add_prime_mul_isIntegral_eq
  [Group G] [Fintype G]
  {p : ℕ}
  {β : ℂ}
-- given
  (hp : p.Prime)
  (hβ : IsIntegral ℤ β)
  (h : 1 + (p : ℂ) * β = 0) :
-- imply
  False := by
-- proof
  apply BurnsidePaqb.false_of_one_add_prime_mul_isIntegral hp hβ h

/--
[eq_smul_one_of_finrank_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SimplePrime.lean)
-/
@[path]
private lemma eq_smul_one_of_finrank_one_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V}
  {g : G}
-- given
  (hd : Module.finrank ℂ V = 1) :
-- imply
  ρ g = ρ.character g • 1 := by
-- proof
  apply BurnsidePaqb.eq_smul_one_of_finrank_one ρ hd g

/--
[card_eq_prime_of_nontrivial_linear](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SimplePrime.lean)
-/
@[path]
private lemma card_eq_prime_of_nontrivial_linear_eq
  [Group G] [Fintype G] [IsSimpleGroup G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V}
-- given
  (hd : Module.finrank ℂ V = 1)
  (hne : ρ.character ≠ 1) :
-- imply
  ∃ r : ℕ, r.Prime ∧ Fintype.card G = r := by
-- proof
  apply BurnsidePaqb.card_eq_prime_of_nontrivial_linear ρ hd hne

/--
[char_zero_of_nonlinear_of_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SimplePrime.lean)
-/
@[path]
private lemma char_zero_of_nonlinear_of_coprime_eq
  [Group G] [Fintype G] [IsSimpleGroup G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {g : G}
-- given
  (hne1 : g ≠ 1)
  (hd : 1 < Module.finrank ℂ V)
  (hcop : Nat.Coprime (conjClass g).card (Module.finrank ℂ V)) :
-- imply
  ρ.character g = 0 := by
-- proof
  apply BurnsidePaqb.char_zero_of_nonlinear_of_coprime ρ g hne1 hd hcop

/--
[cor6_of_prime_pow_class](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SimplePrime.lean)
-/
@[path]
private lemma cor6_of_prime_pow_class_eq
  [Group G] [Fintype G] [IsSimpleGroup G]
  {g : G}
-- given
  (hg1 : g ≠ 1)
  (hpp : IsPrimePow (conjClass g).card) :
-- imply
  ∃ r : ℕ, r.Prime ∧ Fintype.card G = r := by
-- proof
  apply BurnsidePaqb.cor6_of_prime_pow_class g hg1 hpp


-- created on 2026-10-20
