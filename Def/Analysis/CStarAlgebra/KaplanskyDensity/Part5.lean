/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Theorem.Analysis.CStarAlgebra.KaplanskyDensity.Part4

@[expose] public section

open scoped PointwiseConvergenceCLM
open Topology


namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapCayleyInverse

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scalar inverse Cayley function `t ↦ t / (1 + √(1 - t ^ 2))`. -/
noncomputable def kapG : ℝ → ℝ := fun t => t / (1 + Real.sqrt (1 - t ^ 2))

end KapCayleyInverse
end Analysis.CStarAlgebra.KaplanskyDensityWanted
