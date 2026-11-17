/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Algebra.Polynomial.Roots
public import Theorem.NumberTheory.NetoHigherOrderBernoulli

@[expose] public section

/-! # Neto's symmetry identity for higher-order Bernoulli numbers

This file defines higher-order Bernoulli numbers through their formal exponential generating
series and proves Neto's symmetry identity for them.
-/


namespace MetaMathlibExt

open Finset

noncomputable def neto_choosePolynomial (j : ℕ) : Polynomial ℂ :=
  Polynomial.C (j.factorial : ℂ)⁻¹ * descPochhammer ℂ j

end MetaMathlibExt
