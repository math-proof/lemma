module
public import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Theorem.Analysis.MeasureTheory.Section_1_1_2
open Pointwise


public section

/-- The 2D wedge product (signed area parallelogram factor) of two vectors. -/
abbrev EuclideanSpace'.plane_wedge (x y: EuclideanSpace' 2) := x 1 * y 0 - x 0 * y 1

/-- Exercise 1.1.9  A polytope is the convex hull of a finite set of vertices. -/
abbrev IsPolytope {d:ℕ} (P: Set (EuclideanSpace' d)) : Prop :=
  ∃ (V: Finset (EuclideanSpace' d)), P = convexHull ℝ (V : Set _)

