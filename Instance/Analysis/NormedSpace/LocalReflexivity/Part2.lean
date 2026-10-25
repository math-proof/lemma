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
import Theorem.Analysis.NormedSpace.LocalReflexivity.Part2


namespace FunctionalAnalysis.LocalReflexivityWanted

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable section

/-- Normed group structure on a submodule of the bidual. Stated with ground `R M`
so that typeclass resolution unifies first-order (the generic submodule instances
leave `↥?p` stuck). -/
instance plrNACG_Mp {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))) :
    NormedAddCommGroup ↥Mp :=
  @Submodule.normedAddCommGroup 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) _ _ _ Mp

/-- Normed space structure on a submodule of the bidual. -/
instance plrNS_Mp {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))) : NormedSpace 𝕜 ↥Mp :=
  @Submodule.normedSpace 𝕜 𝕜 _ _ _
    (StrongDual 𝕜 (StrongDual 𝕜 E)) _ _ _ _ Mp

/-- Normed group structure on the `M₀` submodule. -/
instance plrNACG_M0 {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))) :
    NormedAddCommGroup ↥(plr_M0 Mp) :=
  @Submodule.normedAddCommGroup 𝕜 ↥Mp _ _ _ (plr_M0 Mp)

/-- Normed group structure on a complement submodule. -/
instance plrNACG_C {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    (C : Submodule 𝕜 ↥Mp) : NormedAddCommGroup ↥C :=
  @Submodule.normedAddCommGroup 𝕜 ↥Mp _ _ _ C

/-- A finite-dimensional submodule of the bidual is a proper metric space. -/
instance plrProper_Mp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp] : ProperSpace ↥Mp :=
  FiniteDimensional.proper_rclike 𝕜 ↥Mp

end
end FunctionalAnalysis.LocalReflexivityWanted
