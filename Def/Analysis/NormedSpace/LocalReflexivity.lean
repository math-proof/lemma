/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Theorem.Analysis.NormedSpace.LocalReflexivity


namespace FunctionalAnalysis.LocalReflexivityWanted

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable section

/-- The subspace of `M'` consisting of points in the range of `J`. -/
def plr_M0 {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))) : Submodule 𝕜 ↥Mp :=
  (LinearMap.range (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap).comap
    Mp.subtype

/-- The inverse of `J` on `M₀`, as a linear map. -/
noncomputable def plr_S0 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))) :
    ↥(plr_M0 Mp) →ₗ[𝕜] E :=
  (LinearEquiv.ofInjective (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap
    plr_J_inj).symm.toLinearMap.comp
    (LinearMap.codRestrict
      (LinearMap.range (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap)
      (Mp.subtype.comp (plr_M0 Mp).subtype) (fun u => u.prop))

end
end FunctionalAnalysis.LocalReflexivityWanted
