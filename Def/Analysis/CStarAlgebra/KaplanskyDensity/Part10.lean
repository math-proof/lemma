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
public import Theorem.Analysis.CStarAlgebra.KaplanskyDensity.Part9
open scoped PointwiseConvergenceCLM
open Topology


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapGamma

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The `(1,2)` corner map `SOT(H ⊕ H) → SOT(H)`. -/
noncomputable def kapGamma (P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H)) :
    H →Lₚₜ[ℂ] H :=
  kapOfBounded (kapFst ∘L toBounded P ∘L kapInr)

end KapGamma
end Analysis.CStarAlgebra.KaplanskyDensityWanted
