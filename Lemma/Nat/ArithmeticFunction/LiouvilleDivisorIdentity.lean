import Mathlib
import sympy.Basic
import Def.NumberTheory.ArithmeticFunction.LiouvilleDivisorIdentity
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[tau_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma tau_prime_pow {p : ℕ} (hp : Nat.Prime p) (j : ℕ) :
  (p ^ j).divisors.card = j + 1 := by
  rw [Nat.divisors_prime_pow hp j, Finset.card_map, Finset.card_range]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[two_mul_sum_range_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma two_mul_sum_range_succ (n : ℕ) :
  2 * ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sum_cube_eq_sq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma sum_cube_eq_sq_sum (n : ℕ) :
  (∑ i ∈ Finset.range n, (i + 1)) ^ 2 = ∑ i ∈ Finset.range n, (i + 1) ^ 3 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h2 : 2 * ∑ i ∈ Finset.range k, (i + 1) = k * (k + 1) :=
      two_mul_sum_range_succ k
    nlinarith [ih, h2, Nat.zero_le k, sq_nonneg (∑ i ∈ Finset.range k, (i + 1)),
      sq_nonneg (k + 1 : ℕ)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[tauCube_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma tauCube_apply (n : ℕ) : tauCube n = (n.divisors.card) ^ 3 :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[tauCube_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma tauCube_mul {m n : ℕ} (h : m.Coprime n) :
  tauCube (m * n) = tauCube m * tauCube n := by
  change ((m * n).divisors.card) ^ 3 = (m.divisors.card) ^ 3 * (n.divisors.card) ^ 3
  rw [Nat.Coprime.card_divisors_mul h]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[tauCube_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma tauCube_one : tauCube 1 = 1 := by
  change (Nat.divisors 1).card ^ 3 = 1
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[tauCube_isMult](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma tauCube_isMult : tauCube.IsMultiplicative :=
  ⟨tauCube_one, fun h => tauCube_mul h⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[F_isMult](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma F_isMult : F.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.mul
    ArithmeticFunction.isMultiplicative_sigma ArithmeticFunction.isMultiplicative_zeta

end MetaMathlibExt

namespace MetaMathlibExt

/--
[G_isMult](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma G_isMult : G.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.mul
    tauCube_isMult ArithmeticFunction.isMultiplicative_zeta

end MetaMathlibExt

namespace MetaMathlibExt

/--
[F_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma F_apply (x : ℕ) : F x = ∑ i ∈ x.divisors, i.divisors.card := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (R := ℕ)
    (f := ArithmeticFunction.sigma 0) (x := x)
  simpa [F, ArithmeticFunction.sigma_zero_apply] using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[G_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma G_apply (x : ℕ) : G x = ∑ i ∈ x.divisors, (i.divisors.card) ^ 3 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (R := ℕ) (f := tauCube) (x := x)
  simpa [G, tauCube_apply] using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Fsq_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma Fsq_apply (n : ℕ) : Fsq n = (F n) ^ 2 :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Fsq_isMult](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma Fsq_isMult : Fsq.IsMultiplicative := by
  constructor
  · change (F 1) ^ 2 = 1
    have h1 : F 1 = 1 := F_isMult.1
    rw [h1, one_pow]
  · intro m n h
    change (F (m * n)) ^ 2 = (F m) ^ 2 * (F n) ^ 2
    rw [F_isMult.2 h]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[prime_pow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma prime_pow_eq {p i : ℕ} (hp : Nat.Prime p) : Fsq (p ^ i) = G (p ^ i) := by
  rw [Fsq_apply, F_apply, G_apply]
  rw [Nat.divisors_prime_pow hp i, Finset.sum_map, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have e1 : (∑ x ∈ Finset.range (i + 1), ((p ^ x).divisors.card)) =
    ∑ x ∈ Finset.range (i + 1), (x + 1) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [tau_prime_pow hp x]
  have e2 : (∑ x ∈ Finset.range (i + 1), (((p ^ x).divisors.card) ^ 3)) =
    ∑ x ∈ Finset.range (i + 1), (x + 1) ^ 3 := by
    apply Finset.sum_congr rfl
    intro x _
    rw [tau_prime_pow hp x]
  rw [e1, e2]
  have h := sum_cube_eq_sq_sum (i + 1)
  rw [h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[FG_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma FG_eq : Fsq = G := by
  have h := (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    Fsq Fsq_isMult G G_isMult).mpr (fun p i hp => prime_pow_eq hp)
  exact h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[liouville_divisor_function_identity_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
lemma liouville_divisor_function_identity_general
  {n : ℕ} :
-- imply
  (∑ d ∈ n.divisors, d.divisors.card) ^ 2 =
    ∑ d ∈ n.divisors, (d.divisors.card) ^ 3 := by
-- proof
  have h := congrArg (fun f => f n) FG_eq
  rwa [Fsq_apply, F_apply, G_apply] at h
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[liouville_divisor_function_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
lemma liouville_divisor_function_identity
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (∑ d ∈ n.divisors, d.divisors.card) ^ 2 =
    ∑ d ∈ n.divisors, (d.divisors.card) ^ 3 := by
-- proof
  exact liouville_divisor_function_identity_general n

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
