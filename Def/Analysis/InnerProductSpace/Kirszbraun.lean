/-
Authors: toskua, Avocado, Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Analysis.InnerProductSpace.Kirszbraun

@[expose] public section

open Finset
open scoped InnerProductSpace


noncomputable def kirszbraunPotential
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Fintype ι] (K : ℝ) (x : E) (xs : ι → E) (ys : ι → F) (a : ι → ℝ) : ℝ :=
  ∑ j, a j * ‖ys j‖ ^ 2 - ‖∑ j, a j • ys j‖ ^ 2 - K ^ 2 * ∑ j, a j * ‖x - xs j‖ ^ 2

