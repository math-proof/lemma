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
public import Def.Analysis.NormedSpace.LocalReflexivity

public section

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
