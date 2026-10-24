/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/WeightedLargeSieve.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.atlas.NumberTheory.PrimeCounting.WeightedHilbert
import Lemma.Nat.PrimeCounting.WeightedHilbert
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Weighted large sieve

The weighted large-sieve inequality obtained from the weighted Hilbert
inequality and the exact finite geometric sum.
-/

open scoped BigOperators ComplexConjugate

namespace MathlibExt.NumberTheory.PrimeCounting

private noncomputable def btAddChar (t : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)
end MathlibExt.NumberTheory.PrimeCounting
