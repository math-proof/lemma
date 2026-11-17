/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Data.List.GetD
public import Mathlib.Basic.Real.Sign
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Theorem.Analysis.NormedSpace.KreinSmulian

@[expose] public section

namespace FunctionalAnalysis.BanachSpaceWanted

open Set Metric

open scoped ComplexConjugate ZeroAtInfty

/-- The coordinate map into `C₀(ℕ × ℕ, ℝ)`. -/
noncomputable def ks_c0fun {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {x : ℕ × ℕ → E}
    (hx0 : Filter.Tendsto x Filter.cofinite (nhds 0)) (φ : WeakDual 𝕜 E) : C₀(ℕ × ℕ, ℝ) :=
  ZeroAtInftyContinuousMap.mk
    ⟨fun p => RCLike.re (φ (x p)), continuous_of_discreteTopology⟩ (by
    have hcont : Continuous fun y : E => RCLike.re (φ y) :=
      RCLike.continuous_re.comp (WeakDual.toStrongDual φ).continuous
    have h0 : RCLike.re (φ 0) = 0 := by simp
    have hcomp := (hcont.tendsto 0).comp hx0
    rw [h0] at hcomp
    rw [Filter.cocompact_eq_cofinite]
    exact hcomp)

end FunctionalAnalysis.BanachSpaceWanted
