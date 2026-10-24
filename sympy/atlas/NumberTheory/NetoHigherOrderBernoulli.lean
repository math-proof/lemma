/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Polynomial.Roots

/-! # Neto's symmetry identity for higher-order Bernoulli numbers

This file defines higher-order Bernoulli numbers through their formal exponential generating
series and proves Neto's symmetry identity for them.
-/

namespace MetaMathlibExt

open Finset

private theorem neto_hasSubst_bernoulli_sub_one :
    PowerSeries.HasSubst (bernoulliPowerSeries ℂ - 1 : PowerSeries ℂ) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero'
  simp [bernoulliPowerSeries]

private noncomputable def neto_choosePolynomial (j : ℕ) : Polynomial ℂ :=
  Polynomial.C (j.factorial : ℂ)⁻¹ * descPochhammer ℂ j

private theorem neto_choose_eq_eval (x : ℂ) (j : ℕ) :
    Ring.choose x j = Polynomial.eval x (neto_choosePolynomial j) := by
  rw [Ring.choose_eq_smul]
  simp only [neto_choosePolynomial, smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_C]
  rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval,
    ← descPochhammer_eval_eq_ascPochhammer]

private theorem neto_coeff_pow_bernoulli_sub_one_eq_zero {m j : ℕ} (h : m < j) :
    PowerSeries.coeff m ((bernoulliPowerSeries ℂ - 1) ^ j) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero j ?_)
  · exact_mod_cast h
  · simp [bernoulliPowerSeries]

private theorem neto_coeff_subst_binomial (x : ℂ) (m : ℕ) :
    PowerSeries.coeff m
        (PowerSeries.subst (bernoulliPowerSeries ℂ - 1)
          (PowerSeries.binomialSeries ℂ x)) =
      ∑ j ∈ Finset.range (m + 1), Ring.choose x j *
        PowerSeries.coeff m ((bernoulliPowerSeries ℂ - 1) ^ j) := by
  rw [PowerSeries.coeff_subst' neto_hasSubst_bernoulli_sub_one]
  have hs : Function.support (fun j : ℕ =>
      PowerSeries.coeff j (PowerSeries.binomialSeries ℂ x) •
        PowerSeries.coeff m ((bernoulliPowerSeries ℂ - 1) ^ j)) ⊆
      (Finset.range (m + 1) : Set ℕ) := by
    intro j hj
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    apply hj
    have hmj : m < j := by omega
    change PowerSeries.coeff j (PowerSeries.binomialSeries ℂ x) •
      PowerSeries.coeff m ((bernoulliPowerSeries ℂ - 1) ^ j) = 0
    rw [neto_coeff_pow_bernoulli_sub_one_eq_zero hmj, smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hs]
  simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]

/-- Higher-order Bernoulli number `B_n^(α) = B_n^(α)(0)`.

The generalized polynomial `B_n^(α)(x)` is given by the source exponential
generating function `∑ n = 0 to ∞ B_n^(α)(x) t^n / n! = (t / (e^t - 1))^α e^(t x)`.

This is an explicit implementation obligation for the JIS source below, with `α : ℂ`
and `n : ℕ`.

Source: https://cs.uwaterloo.ca/journals/JIS/VOL23/Chellal/chellal7.tex
Definition span: lines 99-112,
text_sha256 `0acb659f24f1fa6140d178c11f64ab833f8d8a20336d0828a32665f37f2b7951`.
File sha256 `ce83119262833b8219cb7670521e7602617dae3f645a76e913bff79b7ba7dc9c`. -/
noncomputable def higherOrderBernoulliNumber (α : ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ) * PowerSeries.coeff n
    (PowerSeries.subst (bernoulliPowerSeries ℂ - 1) (PowerSeries.binomialSeries ℂ α))

/-- At a natural order, higher-order Bernoulli numbers are the normalized coefficients of the
corresponding natural power of the Bernoulli generating series. -/
theorem higherOrderBernoulliNumber_nat (d n : ℕ) :
    higherOrderBernoulliNumber (d : ℂ) n =
      (n.factorial : ℂ) * PowerSeries.coeff n (bernoulliPowerSeries ℂ ^ d) := by
  rw [higherOrderBernoulliNumber, PowerSeries.binomialSeries_nat]
  rw [PowerSeries.subst_pow neto_hasSubst_bernoulli_sub_one]
  congr 2
  have hone : PowerSeries.subst (bernoulliPowerSeries ℂ - 1) (1 : PowerSeries ℂ) = 1 := by
    rw [← PowerSeries.coe_substAlgHom neto_hasSubst_bernoulli_sub_one, map_one]
  rw [PowerSeries.subst_add neto_hasSubst_bernoulli_sub_one,
    PowerSeries.subst_X neto_hasSubst_bernoulli_sub_one, hone]
  ring

private theorem neto_higherOrderBernoulliNumber_polynomial (m : ℕ) :
    ∃ P : Polynomial ℂ, ∀ x : ℂ,
      higherOrderBernoulliNumber x m = Polynomial.eval x P := by
  let P : Polynomial ℂ :=
    Polynomial.C (m.factorial : ℂ) *
      ∑ j ∈ Finset.range (m + 1), neto_choosePolynomial j *
        Polynomial.C (PowerSeries.coeff m ((bernoulliPowerSeries ℂ - 1) ^ j))
  refine ⟨P, ?_⟩
  intro x
  rw [higherOrderBernoulliNumber, neto_coeff_subst_binomial]
  simp_rw [neto_choose_eq_eval]
  simp only [P, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]

private noncomputable def neto_higherOrderBernoulliPolynomial (m : ℕ) : Polynomial ℂ :=
  Classical.choose (neto_higherOrderBernoulliNumber_polynomial m)

private theorem neto_higherOrderBernoulliPolynomial_eval (x : ℂ) (m : ℕ) :
    Polynomial.eval x (neto_higherOrderBernoulliPolynomial m) =
      higherOrderBernoulliNumber x m := by
  symm
  exact Classical.choose_spec (neto_higherOrderBernoulliNumber_polynomial m) x

/-- Neto identity for higher-order Bernoulli numbers from the JIS source below.

For `x : ℂ` simultaneously the order and scalar base, and `n ℓ : ℕ`, with
inclusive upper bounds `Finset.range (n + 1)` and `Finset.range (ℓ + 1)`,
natural exponents, and sign `(-1)^(n + ℓ)`.

Source: https://cs.uwaterloo.ca/journals/JIS/VOL23/Chellal/chellal7.tex
Identity span: lines 662-670,
text_sha256 `06790ccab662e77ae848bda8ff92dac6a404d8b43042d433d80c6dd7b127c56f`.
File sha256 `ce83119262833b8219cb7670521e7602617dae3f645a76e913bff79b7ba7dc9c`.

Proves `Wanted` entry `neto_higher_order_bernoulli_identity`.

Proof: The substitution coefficient formula makes both sides polynomial in the order. For natural
orders, the cited Bernoulli EGF gives the reflection identity, formal differentiation proves Neto's
formula, and equality on all natural complex points finishes the polynomial argument.
-/
theorem neto_higher_order_bernoulli_identity (x : ℂ) (n ℓ : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      x ^ (n - k) * (Nat.choose n k : ℂ) * higherOrderBernoulliNumber x (ℓ + k)) =
    (-1 : ℂ) ^ (n + ℓ) *
      ∑ k ∈ Finset.range (ℓ + 1),
        x ^ (ℓ - k) * (Nat.choose ℓ k : ℂ) * higherOrderBernoulliNumber x (n + k) := by
  let P : Polynomial ℂ :=
    ∑ k ∈ range (n + 1), Polynomial.X ^ (n - k) * Polynomial.C (n.choose k : ℂ) *
      neto_higherOrderBernoulliPolynomial (ℓ + k)
  let Q : Polynomial ℂ :=
    Polynomial.C ((-1 : ℂ) ^ (n + ℓ)) *
      ∑ k ∈ range (ℓ + 1), Polynomial.X ^ (ℓ - k) *
        Polynomial.C (ℓ.choose k : ℂ) * neto_higherOrderBernoulliPolynomial (n + k)
  have hP (y : ℂ) : Polynomial.eval y P =
      ∑ k ∈ range (n + 1), y ^ (n - k) * (n.choose k : ℂ) *
        higherOrderBernoulliNumber y (ℓ + k) := by
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, neto_higherOrderBernoulliPolynomial_eval]
  have hQ (y : ℂ) : Polynomial.eval y Q =
      (-1 : ℂ) ^ (n + ℓ) *
        ∑ k ∈ range (ℓ + 1), y ^ (ℓ - k) * (ℓ.choose k : ℂ) *
          higherOrderBernoulliNumber y (n + k) := by
    simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, neto_higherOrderBernoulliPolynomial_eval]
  have heval_nat (d : ℕ) : Polynomial.eval (d : ℂ) P = Polynomial.eval (d : ℂ) Q := by
    rw [hP, hQ]
    exact neto_identity_nat d n ℓ
  have hrange : (Set.range (fun d : ℕ => (d : ℂ))).Infinite :=
    Set.infinite_range_of_injective Nat.cast_injective
  have hinf : {y : ℂ | Polynomial.eval y P = Polynomial.eval y Q}.Infinite := by
    apply hrange.mono
    rintro y ⟨d, rfl⟩
    exact heval_nat d
  have hPQ : P = Q := Polynomial.eq_of_infinite_eval_eq P Q hinf
  calc
    _ = Polynomial.eval x P := (hP x).symm
    _ = Polynomial.eval x Q := congrArg (Polynomial.eval x) hPQ
    _ = _ := hQ x

end MetaMathlibExt
