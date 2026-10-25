/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Theorem.Analysis.CStarAlgebra.KaplanskyDensity.Part3
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
