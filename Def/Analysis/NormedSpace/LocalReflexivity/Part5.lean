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
import Theorem.Analysis.NormedSpace.LocalReflexivity.Part5


namespace FunctionalAnalysis.LocalReflexivityWanted

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable section

/-- The operator `T'` on `M'`, as a linear map. -/
def plr_T'lin {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (y : Fin (Module.finrank 𝕜 ↥C) → E) : ↥Mp →ₗ[𝕜] E where
  toFun u := plr_S0 Mp (plr_pi0 Mp C hC u)
    + ∑ j, (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC u) j • y j
  map_add' u v := by
    have e1 : plr_pi0 Mp C hC (u + v)
        = plr_pi0 Mp C hC u + plr_pi0 Mp C hC v := map_add _ _ _
    have e2 : plr_pi1 Mp C hC (u + v)
        = plr_pi1 Mp C hC u + plr_pi1 Mp C hC v := map_add _ _ _
    simp only [e1, e2, map_add, Finsupp.add_apply, add_smul,
      Finset.sum_add_distrib]
    abel
  map_smul' c u := by
    have e1 : plr_pi0 Mp C hC (c • u) = c • plr_pi0 Mp C hC u :=
      map_smul _ _ _
    have e2 : plr_pi1 Mp C hC (c • u) = c • plr_pi1 Mp C hC u :=
      map_smul _ _ _
    simp only [e1, e2, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_smul,
      RingHom.id_apply, smul_add, Finset.smul_sum]

/-- The operator `T'` on `M'`, continuous. -/
noncomputable def plr_T' {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (y : Fin (Module.finrank 𝕜 ↥C) → E) : ↥Mp →L[𝕜] E :=
  LinearMap.toContinuousLinearMap (plr_T'lin Mp C hC y)

end
end FunctionalAnalysis.LocalReflexivityWanted
