/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Data.List.GetD
import Mathlib.Basic.Real.Sign
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Def.Analysis.NormedSpace.KreinSmulian.Part2


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
