import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_2.Part2
open Pointwise


/-- Two sets are isometric if one is an orthogonal transformation plus translation of the other. -/
abbrev Isometric {d:ℕ} (E F: Set (EuclideanSpace' d)) : Prop :=
 ∃ A ∈ Matrix.orthogonalGroup (Fin d) ℝ, ∃ x₀, F = ((fun x => WithLp.toLp 2 (Matrix.toLin' A x.ofLp)) '' E) + {x₀}

/-- The unit square with all rational points removed (not Jordan measurable). -/
abbrev bullet_riddled_square : Set (EuclideanSpace' 2) := { x | ∀ i, x i ∈ Set.Icc 0 1 ∧ x i ∉ (fun (q:ℚ) ↦ (q:ℝ)) '' .univ}

/-- The set of rational points in the unit square (not Jordan measurable). -/
abbrev bullets : Set (EuclideanSpace' 2) := { x | ∀ i, x i ∈ Set.Icc 0 1 ∧ x i ∈ (fun (q:ℚ) ↦ (q:ℝ)) '' .univ}

