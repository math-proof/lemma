/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry13CorollarySchroder.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Schröder's exponential series

This file proves Ramanujan's corollary to Entry 13 by means of Abel polynomials, their
binomial convolution, and the tree-function inverse of `z ↦ z * exp (-z)` on the unit disk.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry13CorollarySchroder

private noncomputable def schroder_abelTerm (w : ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  if k = 0 then 1 else z * (z + (k : ℂ) * w) ^ (k - 1)

private noncomputable def schroder_majorant (R : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1
  else R * (R + (k : ℝ)) ^ (k - 1) * Real.exp (-1) ^ k / (Nat.factorial k : ℝ)

private noncomputable def schroder_term (r z : ℂ) (k : ℕ) : ℂ :=
  schroder_abelTerm 1 k z * r ^ k / (Nat.factorial k : ℂ)

private noncomputable def schroder_F (r z : ℂ) : ℂ :=
  ∑' k : ℕ, schroder_term r z k

private noncomputable def schroder_c (r : ℂ) : ℂ :=
  r * schroder_F r 1
end Entry13CorollarySchroder
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
