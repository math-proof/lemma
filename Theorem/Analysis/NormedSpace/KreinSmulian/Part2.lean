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
public import Def.Analysis.NormedSpace.KreinSmulian.Part2

public section

namespace FunctionalAnalysis.BanachSpaceWanted

open Set Metric

open scoped ComplexConjugate ZeroAtInfty

/-- Values of the coordinate map. -/
lemma ks_c0fun_apply {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {x : ℕ × ℕ → E}
    (hx0 : Filter.Tendsto x Filter.cofinite (nhds 0)) (φ : WeakDual 𝕜 E) (p : ℕ × ℕ) :
    ks_c0fun hx0 φ p = RCLike.re (φ (x p)) :=
  rfl

end FunctionalAnalysis.BanachSpaceWanted
