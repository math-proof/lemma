module
public import Mathlib.Topology.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Choose.Basic
public import Theorem.Analysis.Asymptotics.CatalanAsymptoticExpansion.Part8
public import Theorem.Real.Asymptotics.CatalanAsymptoticExpansion
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Asymptotics/CatalanOddTermsShift.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# The unique even-power shift for Catalan asymptotics

This file proves that `3/4` is the unique shift for which the normalized
Catalan numbers have an all-orders expansion containing only even powers.
-/
namespace MetaMathlibExt

open scoped BigOperators

noncomputable def catalanOddShiftLogCoeff (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ (j + 2) *
    (Polynomial.aeval (-1 / 4 : ℝ) (Polynomial.bernoulli (j + 2)) -
      Polynomial.aeval (5 / 4 : ℝ) (Polynomial.bernoulli (j + 2))) /
      ((j + 1 : ℕ) * (j + 2 : ℕ))

noncomputable def catalanOddShiftLogPoly (M : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, catalanOddShiftLogCoeff j * x ^ (j + 1)

noncomputable def catalanOddShiftExpCoeff (M k : ℕ) : ℝ :=
  iteratedDeriv k (fun x : ℝ => Real.exp (catalanOddShiftLogPoly M x)) 0 /
    k.factorial

noncomputable def catalanOddShiftU (n : ℕ) : ℝ := (n : ℝ) + 3 / 4

noncomputable def catalanOddShiftY (n : ℕ) : ℝ := 1 / catalanOddShiftU n

noncomputable def catalanOddShiftG (n : ℕ) : ℝ :=
  (catalan n : ℝ) * Real.sqrt (Real.pi * catalanOddShiftU n ^ 3) / (4 : ℝ) ^ n

noncomputable def catalanOddShiftCoeff (k : ℕ) : ℝ :=
  catalanOddShiftExpCoeff k k

noncomputable def catalanOddShiftF (c : ℝ) (n : ℕ) : ℝ :=
  (Nat.choose (2 * n) n : ℝ) / ((n : ℝ) + 1) * Real.sqrt Real.pi *
    Real.rpow ((n : ℝ) + c) ((3 : ℝ) / 2) / (4 : ℝ) ^ n

noncomputable def catalanOddShiftFirstLogCoeff (c : ℝ) : ℝ :=
  (Polynomial.aeval (1 / 2 - c) (Polynomial.bernoulli 2) -
    Polynomial.aeval (2 - c) (Polynomial.bernoulli 2)) / 2

end MetaMathlibExt
