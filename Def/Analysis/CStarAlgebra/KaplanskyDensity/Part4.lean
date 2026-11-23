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
public import Theorem.Analysis.CStarAlgebra.KaplanskyDensity.Part3

@[expose] public section

open scoped PointwiseConvergenceCLM
open Topology


namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapCayley

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scalar resolvent function `t ↦ (1 + t ^ 2)⁻¹`. -/
noncomputable def kapR : ℝ → ℝ := fun t => (1 + t ^ 2)⁻¹

/-- Scalar Cayley-type function `t ↦ 2 * t / (1 + t ^ 2)`. -/
noncomputable def kapF : ℝ → ℝ := fun t => 2 * t / (1 + t ^ 2)

/-- cfc of `kapR` at `a`. -/
noncomputable def kapCfcR (a : H →L[ℂ] H) : H →L[ℂ] H := cfc kapR a

/-- cfc of `kapF` at `a`. -/
noncomputable def kapCfcF (a : H →L[ℂ] H) : H →L[ℂ] H := cfc kapF a

end KapCayley
end Analysis.CStarAlgebra.KaplanskyDensityWanted
