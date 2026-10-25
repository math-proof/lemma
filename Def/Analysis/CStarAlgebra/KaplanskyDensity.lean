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
import Abbrev.Analysis.CStarAlgebra.KaplanskyDensity
open scoped PointwiseConvergenceCLM
open Topology


namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapPlumbing

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Forward map `B(H) → SOT(H)`, the inverse of `toBounded`. -/
noncomputable def kapOfBounded (T : H →L[ℂ] H) : H →Lₚₜ[ℂ] H :=
  ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) H {s : Set H | Finite s} T

/-- Adjoint read through the SOT equivalence. -/
noncomputable def kapStar (p : H →Lₚₜ[ℂ] H) : H →Lₚₜ[ℂ] H :=
  kapOfBounded (star (toBounded p))

end KapPlumbing
end Analysis.CStarAlgebra.KaplanskyDensityWanted
