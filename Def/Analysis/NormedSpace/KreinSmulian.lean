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


namespace FunctionalAnalysis.BanachSpaceWanted

open Set Metric

open scoped ComplexConjugate ZeroAtInfty

/-! # Krein–Šmulian theorem -/

/-- Real polar of a set `F ⊆ E`: functionals whose real part is at most `1` on `F`. -/
def ks_rpol {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (F : Set E) : Set (WeakDual 𝕜 E) :=
  {φ | ∀ x ∈ F, RCLike.re (φ x) ≤ 1}

end FunctionalAnalysis.BanachSpaceWanted
