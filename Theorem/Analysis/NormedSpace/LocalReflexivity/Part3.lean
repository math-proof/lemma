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
import Def.Analysis.NormedSpace.LocalReflexivity.Part2


namespace FunctionalAnalysis.LocalReflexivityWanted

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable section

/-- The first projection fixes `M₀`. -/
theorem plr_pi0_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (u : ↥(plr_M0 Mp)) :
    plr_pi0 Mp C hC ((plr_M0 Mp).subtype u) = u :=
  Submodule.projectionOnto_apply_left hC u

/-- The second projection vanishes on `M₀`. -/
theorem plr_pi1_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (u : ↥(plr_M0 Mp)) :
    plr_pi1 Mp C hC ((plr_M0 Mp).subtype u) = 0 :=
  Submodule.projectionOnto_apply_right hC.symm u

/-- The two projections sum to the identity on `M'`. -/
theorem plr_add_id {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C) :
    (plr_M0 Mp).subtype.comp (plr_pi0 Mp C hC)
      + C.subtype.comp (plr_pi1 Mp C hC) = LinearMap.id :=
  Submodule.subtype_comp_projectionOnto_add_eq_id hC

/-- Decomposition of a point of `M'` into its `M₀` part and `C` coordinates,
pushed into the bidual. -/
theorem plr_decomp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (m : ↥Mp) :
    Mp.subtype m = (NormedSpace.inclusionInDoubleDual 𝕜 E)
          (plr_S0 Mp (plr_pi0 Mp C hC m))
        + ∑ j, ((Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC m) j)
          • Mp.subtype (C.subtype ((Module.finBasis 𝕜 ↥C) j)) := by
  have hmod : (plr_M0 Mp).subtype (plr_pi0 Mp C hC m)
      + C.subtype (plr_pi1 Mp C hC m) = m := by
    have h := LinearMap.congr_fun (plr_add_id Mp C hC) m
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at h
    exact h
  have hCexp : plr_pi1 Mp C hC m
      = ∑ j, ((Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC m) j)
        • ((Module.finBasis 𝕜 ↥C) j) :=
    (Module.Basis.sum_repr _ _).symm
  have hJ : Mp.subtype ((plr_M0 Mp).subtype (plr_pi0 Mp C hC m))
      = (NormedSpace.inclusionInDoubleDual 𝕜 E)
        (plr_S0 Mp (plr_pi0 Mp C hC m)) :=
    (plr_S0_mem Mp _).symm
  have hbase := congrArg Mp.subtype hmod
  rw [map_add, hCexp, map_sum, map_sum] at hbase
  simp only [map_smul] at hbase
  rw [hJ] at hbase
  exact hbase.symm

end
end FunctionalAnalysis.LocalReflexivityWanted
