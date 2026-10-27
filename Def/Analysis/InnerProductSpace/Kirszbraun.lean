/-
Authors: toskua, Avocado, Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Analysis.InnerProductSpace.Kirszbraun
open Finset
open scoped InnerProductSpace


noncomputable def kirszbraunPotential
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Fintype ι] (K : ℝ) (x : E) (xs : ι → E) (ys : ι → F) (a : ι → ℝ) : ℝ :=
  ∑ j, a j * ‖ys j‖ ^ 2 - ‖∑ j, a j • ys j‖ ^ 2 - K ^ 2 * ∑ j, a j * ‖x - xs j‖ ^ 2

