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
import Theorem.Analysis.CStarAlgebra.KaplanskyDensity.Part5
open scoped PointwiseConvergenceCLM
open Topology


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
