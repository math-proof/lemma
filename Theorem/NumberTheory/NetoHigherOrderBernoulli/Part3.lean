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
import Def.NumberTheory.NetoHigherOrderBernoulli.Part2
/-! # Neto's symmetry identity for higher-order Bernoulli numbers

This file defines higher-order Bernoulli numbers through their formal exponential generating
series and proves Neto's symmetry identity for them.
-/


namespace MetaMathlibExt

open Finset

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

theorem neto_higherOrderBernoulliNumber_polynomial (m : ℕ) :
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

end MetaMathlibExt
