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
import Theorem.Analysis.CStarAlgebra.KaplanskyDensity.Part4
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
