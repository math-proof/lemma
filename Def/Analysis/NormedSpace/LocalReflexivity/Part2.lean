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
import Instance.Analysis.NormedSpace.LocalReflexivity.Part2


namespace FunctionalAnalysis.LocalReflexivityWanted

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable section

/-- First projection of the `M₀ ⊕ C` decomposition inside `M'`. -/
def plr_pi0 {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C) :
    ↥Mp →ₗ[𝕜] ↥(plr_M0 Mp) :=
  (plr_M0 Mp).projectionOnto C hC

/-- Second projection of the `M₀ ⊕ C` decomposition inside `M'`. -/
def plr_pi1 {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C) :
    ↥Mp →ₗ[𝕜] ↥C :=
  C.projectionOnto (plr_M0 Mp) hC.symm

end
end FunctionalAnalysis.LocalReflexivityWanted
