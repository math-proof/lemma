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
import Def.Analysis.NormedSpace.LocalReflexivity


namespace FunctionalAnalysis.LocalReflexivityWanted

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable section

/-- `S₀` inverts `J`: applying `J` after `S₀` recovers the coercion. -/
theorem plr_S0_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    (u : ↥(plr_M0 Mp)) :
    (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap (plr_S0 Mp u)
      = Mp.subtype u.val :=
  LinearEquiv.ofInjective_symm_apply _ (h := plr_J_inj) _

/-- Real part of a finite sum is the sum of the real parts. -/
theorem plr_re_sum {ι : Type*} (s : Finset ι) (F : ι → 𝕜) :
    RCLike.re (∑ i ∈ s, F i) = ∑ i ∈ s, RCLike.re (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty, RCLike.zero_re]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add RCLike.re, ih]

/-- A continuous linear functional on a pi type is the sum of its
single-coordinate composites. -/
theorem plr_clm_pi_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Psi : (ι → E) →L[𝕜] 𝕜) (v : ι → E) :
    Psi v = ∑ k, (Psi.comp (ContinuousLinearMap.single 𝕜 (fun _ => E) k)) (v k) :=
  (ContinuousLinearMap.sum_comp_single 𝕜 (fun _ => E) Psi v).symm

end
end FunctionalAnalysis.LocalReflexivityWanted
