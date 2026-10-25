import Mathlib
import sympy.Basic
import Def.NumberTheory.ArithmeticFunction.DedekindPsi
open Nat Finset
open ArithmeticFunction


namespace ArithmeticFunction

/--
[dedekindPsi_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
lemma dedekindPsi_zero
  :
-- imply
  dedekindPsi (0 : ℕ) = 0 := by
-- proof
  simp [dedekindPsi]

end ArithmeticFunction

namespace ArithmeticFunction

/--
[dedekindPsi_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
lemma dedekindPsi_one
  :
-- imply
  dedekindPsi (1 : ℕ) = 1 := by
-- proof
  simp [dedekindPsi, Nat.factorization_one]

end ArithmeticFunction

namespace ArithmeticFunction

/--
[dedekindPsi_eq_prod_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
lemma dedekindPsi_eq_prod_factorization
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  dedekindPsi n = n.factorization.prod fun p k => p ^ (k - 1) * (p + 1) := by
-- proof
  simp [dedekindPsi, hn]

end ArithmeticFunction

namespace ArithmeticFunction

/--
[dedekindPsi_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
lemma dedekindPsi_prime_pow
  {p k : ℕ}
-- given
  (hp : Nat.Prime p)
  (hk : 0 < k) :
-- imply
  dedekindPsi (p ^ k) = p ^ (k - 1) * (p + 1) := by
-- proof
  rw [dedekindPsi_eq_prod_factorization (pow_ne_zero k hp.ne_zero), hp.factorization_pow]
  have hk_ne : k ≠ 0 := Nat.ne_zero_of_lt hk
  have hside :
    (fun (a b : ℕ) => if b = 0 then (1 : ℕ) else a ^ (b - 1) * (a + 1)) p 0 = 1 := by
    simp
  have hcongr :
    (Finsupp.single p k).prod (fun a b => a ^ (b - 1) * (a + 1)) =
      (Finsupp.single p k).prod
        fun a b => if b = 0 then 1 else a ^ (b - 1) * (a + 1) := by
    apply Finsupp.prod_congr
    intro a ha
    have ha_eq : a = p := by
      rw [Finsupp.support_single p hk_ne] at ha
      simpa using ha
    subst a
    simp [hk_ne]
  rw [hcongr, Finsupp.prod_single_index hside]
  simp [hk_ne]

end ArithmeticFunction

namespace ArithmeticFunction

/--
[dedekindPsi_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
lemma dedekindPsi_prime
  {p : ℕ}
-- given
  (hp : Nat.Prime p) :
-- imply
  dedekindPsi p = p + 1 := by
-- proof
  simpa only [pow_one, Nat.reduceSubDiff, pow_zero, one_mul] using
    dedekindPsi_prime_pow (k := 1) hp Nat.one_pos

end ArithmeticFunction

namespace ArithmeticFunction

/--
[isMultiplicative_dedekindPsi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
lemma isMultiplicative_dedekindPsi
  :
-- imply
  IsMultiplicative dedekindPsi := by
-- proof
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨dedekindPsi_one, fun {m n} hm hn hmn => ?_⟩
  rw [dedekindPsi_eq_prod_factorization hm, dedekindPsi_eq_prod_factorization hn,
    dedekindPsi_eq_prod_factorization (mul_ne_zero hm hn),
    Nat.factorization_mul_of_coprime hmn,
    Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors]

end ArithmeticFunction

namespace ArithmeticFunction

/--
[dedekindPsi_mul_prod_primeFactors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
lemma dedekindPsi_mul_prod_primeFactors
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  dedekindPsi n * ∏ p ∈ n.primeFactors, p = n * ∏ p ∈ n.primeFactors, (p + 1) := by
-- proof
  rw [dedekindPsi_eq_prod_factorization hn]
  have hn_prod : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    calc
      n = n.factorization.prod fun p k => p ^ k := (Nat.prod_factorization_pow_eq_self hn).symm
      _ = ∏ p ∈ n.factorization.support, p ^ n.factorization p := rfl
      _ = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by rw [Nat.support_factorization]
  have hpsi_prod : n.factorization.prod (fun p k => p ^ (k - 1) * (p + 1)) =
    ∏ p ∈ n.primeFactors, (p ^ (n.factorization p - 1) * (p + 1)) := by
    calc
      _ = ∏ p ∈ n.factorization.support,
        (p ^ (n.factorization p - 1) * (p + 1)) := rfl
      _ = _ := by rw [Nat.support_factorization]
  rw [hpsi_prod]
  have hkey : (∏ p ∈ n.primeFactors, (p ^ (n.factorization p - 1) * (p + 1))) *
    (∏ p ∈ n.primeFactors, p) =
    (∏ p ∈ n.primeFactors, p ^ n.factorization p) *
      (∏ p ∈ n.primeFactors, (p + 1)) := by
    rw [← Finset.prod_mul_distrib]
    conv_rhs => rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hmem : p ∈ n.factorization.support := by rwa [Nat.support_factorization]
    have hkpos : 0 < n.factorization p :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmem)
    calc
      (p ^ (n.factorization p - 1) * (p + 1)) * p =
        (p ^ (n.factorization p - 1) * p) * (p + 1) := by ac_rfl
      _ = p ^ n.factorization p * (p + 1) := by rw [Nat.pow_pred_mul hkpos]
  rw [hkey, ← hn_prod]

end ArithmeticFunction

namespace ArithmeticFunction

/--
[dedekindPsi_eq_rational_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
lemma dedekindPsi_eq_rational_prod
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  (dedekindPsi n : ℚ) = (n : ℚ) * ∏ p ∈ n.primeFactors, (1 + (p : ℚ)⁻¹) := by
-- proof
  have hcleared : (dedekindPsi n : ℚ) * ∏ p ∈ n.primeFactors, (p : ℚ) =
    (n : ℚ) * ∏ p ∈ n.primeFactors, ((p : ℚ) + 1) := by
    simpa only [Nat.cast_mul, Nat.cast_prod, Nat.cast_add, Nat.cast_one] using
      congrArg (fun x : ℕ => (x : ℚ)) (dedekindPsi_mul_prod_primeFactors hn)
  have hprod_ne : (∏ p ∈ n.primeFactors, (p : ℚ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
  have hpointwise : ∀ p ∈ n.primeFactors,
    ((p : ℚ) + 1) = (p : ℚ) * (1 + (p : ℚ)⁻¹) := by
    intro p hp
    have hp0 : (p : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
    rw [mul_add, mul_one, mul_inv_cancel₀ hp0]
  have hprod_eq : ∏ p ∈ n.primeFactors, ((p : ℚ) + 1) =
    (∏ p ∈ n.primeFactors, (p : ℚ)) *
      ∏ p ∈ n.primeFactors, (1 + (p : ℚ)⁻¹) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hpointwise
  apply mul_left_cancel₀ hprod_ne
  calc
    (∏ p ∈ n.primeFactors, (p : ℚ)) * (dedekindPsi n : ℚ) =
      (dedekindPsi n : ℚ) * ∏ p ∈ n.primeFactors, (p : ℚ) := mul_comm _ _
    _ = (n : ℚ) * ∏ p ∈ n.primeFactors, ((p : ℚ) + 1) := hcleared
    _ = (n : ℚ) * ((∏ p ∈ n.primeFactors, (p : ℚ)) *
      ∏ p ∈ n.primeFactors, (1 + (p : ℚ)⁻¹)) := by rw [hprod_eq]
    _ = (∏ p ∈ n.primeFactors, (p : ℚ)) *
      ((n : ℚ) * ∏ p ∈ n.primeFactors, (1 + (p : ℚ)⁻¹)) := by ac_rfl

end ArithmeticFunction


-- created on 2026-10-20
-- updated on 2026-10-23
