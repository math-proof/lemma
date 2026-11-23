/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/WeightedLargeSieve.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Def.NumberTheory.PrimeCounting.WeightedHilbert
public import Theorem.Nat.PrimeCounting.WeightedHilbert
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators ComplexConjugate

/-!
# Weighted large sieve

The weighted large-sieve inequality obtained from the weighted Hilbert
inequality and the exact finite geometric sum.
-/


namespace MathlibExt.NumberTheory.PrimeCounting

noncomputable def btAddChar (t : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

end MathlibExt.NumberTheory.PrimeCounting
