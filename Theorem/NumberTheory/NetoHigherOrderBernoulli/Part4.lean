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
import Def.NumberTheory.NetoHigherOrderBernoulli.Part3
/-! # Neto's symmetry identity for higher-order Bernoulli numbers

This file defines higher-order Bernoulli numbers through their formal exponential generating
series and proves Neto's symmetry identity for them.
-/


namespace MetaMathlibExt

open Finset

theorem neto_higherOrderBernoulliPolynomial_eval (x : ℂ) (m : ℕ) :
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
