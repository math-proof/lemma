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
public import Theorem.Analysis.NormedSpace.KreinSmulian.Part2

@[expose] public section

namespace FunctionalAnalysis.BanachSpaceWanted

open Set Metric

open scoped ComplexConjugate ZeroAtInfty

/-- The coordinate map as a real linear map. -/
noncomputable def ks_c0lin {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {x : ℕ × ℕ → E}
    (hx0 : Filter.Tendsto x Filter.cofinite (nhds 0)) : WeakDual 𝕜 E →ₗ[ℝ] C₀(ℕ × ℕ, ℝ) where
  toFun := ks_c0fun hx0
  map_add' := fun φ ψ => by
    ext p
    simp only [ks_c0fun_apply, ZeroAtInftyContinuousMap.add_apply]
    have hadd : (φ + ψ) (x p) = φ (x p) + ψ (x p) := rfl
    rw [hadd]
    exact ks_re_add _ _
  map_smul' := fun c φ => by
    ext p
    simp only [ks_c0fun_apply, ZeroAtInftyContinuousMap.smul_apply]
    have hsmul : ((c • φ) (x p)) = c • (φ (x p)) := rfl
    rw [hsmul, RCLike.smul_re]
    simp only [smul_eq_mul, RingHom.id_apply]

end FunctionalAnalysis.BanachSpaceWanted
