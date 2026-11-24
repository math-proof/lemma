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
public import Theorem.Analysis.CStarAlgebra.KaplanskyDensity.Part8
open scoped PointwiseConvergenceCLM
open Topology


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapPsi

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The pair-to-corner map `SOT(H) × SOT(H) → SOT(H ⊕ H)`. -/
noncomputable def kapPsi (p q : H →Lₚₜ[ℂ] H) :
    WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) :=
  kapOfBounded (kapInl ∘L toBounded p ∘L kapSnd + kapInr ∘L toBounded q ∘L kapFst)

end KapPsi
end Analysis.CStarAlgebra.KaplanskyDensityWanted
