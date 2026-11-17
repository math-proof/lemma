/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Theorem.Analysis.NormedSpace.LocalReflexivity

@[expose] public section

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
