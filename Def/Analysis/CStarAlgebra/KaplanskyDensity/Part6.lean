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
public import Theorem.Analysis.CStarAlgebra.KaplanskyDensity.Part5
open scoped PointwiseConvergenceCLM
open Topology


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapL2Prod

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- First projection `WithLp 2 (H × H) →L[ℂ] H`. -/
noncomputable def kapFst : WithLp 2 (H × H) →L[ℂ] H :=
  WithLp.fstL 2 ℂ H H

/-- Second projection. -/
noncomputable def kapSnd : WithLp 2 (H × H) →L[ℂ] H :=
  WithLp.sndL 2 ℂ H H

/-- First inclusion `H →L[ℂ] WithLp 2 (H × H)`. -/
noncomputable def kapInl : H →L[ℂ] WithLp 2 (H × H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl ℂ H H

/-- Second inclusion. -/
noncomputable def kapInr : H →L[ℂ] WithLp 2 (H × H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℂ H H

end KapL2Prod
end Analysis.CStarAlgebra.KaplanskyDensityWanted
