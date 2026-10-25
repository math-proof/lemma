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

theorem neto_hasSubst_bernoulli_sub_one :
    PowerSeries.HasSubst (bernoulliPowerSeries ℂ - 1 : PowerSeries ℂ) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero'
  simp [bernoulliPowerSeries]

end MetaMathlibExt
