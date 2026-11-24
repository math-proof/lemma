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
public import Def.Analysis.CStarAlgebra.KaplanskyDensity.Part7
open scoped PointwiseConvergenceCLM
open Topology


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapCorner

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Membership in `kapCorner` unfolds definitionally. -/
theorem kapMem_corner (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) :
    T ∈ kapCorner S ↔ kapFst ∘L T ∘L kapInl ∈ S ∧ kapFst ∘L T ∘L kapInr ∈ S ∧
      kapSnd ∘L T ∘L kapInl ∈ S ∧ kapSnd ∘L T ∘L kapInr ∈ S :=
  Iff.rfl

end KapCorner
end Analysis.CStarAlgebra.KaplanskyDensityWanted
