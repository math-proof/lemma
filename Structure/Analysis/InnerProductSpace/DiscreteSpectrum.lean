/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DiscreteSpectrum.lean -/

/-
Author: Muse Spark 1.3
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
open scoped BigOperators


/-- A generic nonnegative discrete spectrum: a zero-based eigenvalue sequence,
counted with multiplicity by index, diverging to `+∞`.

This is a transform layer only. It does not claim that an arbitrary sequence
is a Dirichlet or Neumann Laplacian spectrum; connecting a sequence to an
operator is left to a later domain-specific construction. -/
structure NonnegativeDiscreteSpectrum where
  eigenvalue : ℕ → ℝ
  nonnegative_eigenvalue : ∀ j, 0 ≤ eigenvalue j
  monotone_eigenvalue : Monotone eigenvalue
  tendsto_eigenvalue_atTop :
    Filter.Tendsto eigenvalue Filter.atTop Filter.atTop

