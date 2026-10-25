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
import Def.Analysis.CStarAlgebra.KaplanskyDensity.Part7
open scoped PointwiseConvergenceCLM
open Topology


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
