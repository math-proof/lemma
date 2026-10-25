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
import Theorem.NumberTheory.NetoHigherOrderBernoulli.Part2
/-! # Neto's symmetry identity for higher-order Bernoulli numbers

This file defines higher-order Bernoulli numbers through their formal exponential generating
series and proves Neto's symmetry identity for them.
-/


namespace MetaMathlibExt

open Finset

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

end MetaMathlibExt
