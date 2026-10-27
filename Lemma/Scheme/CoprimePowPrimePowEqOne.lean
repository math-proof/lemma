import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma zpow_mul_zpow_eq_self
  {G : Type} [Group G] (g : G) (x y m q : ℤ)
  (hxy : x * m + y * q = 1) :
  g ^ (y * q) * g ^ (x * m) = g := by
  rw [← zpow_add, show y * q + x * m = 1 by linarith, zpow_one]
private lemma zpow_mul_orderOf_mul
  (G : Type) [Group G] (g : G) (c : ℤ) :
  g ^ (c * (orderOf g : ℤ)) = 1 := by
  rw [mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
/--
[exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one.lean)
-/
@[path]
private lemma main
  (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G] (g : G) :
  -- imply
  ∃ g' u : G, g' * u = g ∧ Commute g' u ∧ (orderOf g').Coprime p ∧ (∃ a : ℕ, u ^ p ^ a = 1) ∧
    g' ∈ Subgroup.zpowers g ∧ u ∈ Subgroup.zpowers g := by
  -- proof
  have hp : p.Prime := Fact.out
  have hn0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hqm : p ^ (orderOf g).factorization p * (orderOf g / p ^ (orderOf g).factorization p) =
      orderOf g := Nat.ordProj_mul_ordCompl_eq_self (orderOf g) p
  have hcop : (orderOf g / p ^ (orderOf g).factorization p).Coprime p :=
    (Nat.coprime_ordCompl hp hn0).symm
  set a : ℕ := (orderOf g).factorization p with ha
  set q : ℕ := p ^ a with hq
  set m : ℕ := orderOf g / q with hm
  have hmq : m.Coprime q := hcop.pow_right a
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.mpr hmq
  have hqmZ : (q : ℤ) * (m : ℤ) = (orderOf g : ℤ) := by exact_mod_cast hqm
  refine ⟨g ^ (y * q), g ^ (x * m), zpow_mul_zpow_eq_self g x y m q hxy,
    Commute.zpow_zpow_self g _ _, ?_, ⟨a, ?_⟩,
    Subgroup.mem_zpowers_iff.mpr ⟨_, rfl⟩, Subgroup.mem_zpowers_iff.mpr ⟨_, rfl⟩⟩
  ·
    have h1 : (g ^ ((y : ℤ) * q)) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_assoc, hqmZ]
      refine zpow_mul_orderOf_mul G g y
    refine Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1) hcop
  ·
    show (g ^ ((x : ℤ) * m)) ^ q = 1
    rw [← zpow_natCast, ← zpow_mul, mul_assoc, mul_comm (m : ℤ), hqmZ]
    refine zpow_mul_orderOf_mul G g x


-- created on 2026-10-20
