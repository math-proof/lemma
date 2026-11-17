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

@[expose] public section

namespace FunctionalAnalysis.BanachSpaceWanted

open Set Metric

open scoped ComplexConjugate ZeroAtInfty

/-! # Krein–Šmulian theorem -/

/-- Real polar of a set `F ⊆ E`: functionals whose real part is at most `1` on `F`. -/
def ks_rpol {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (F : Set E) : Set (WeakDual 𝕜 E) :=
  {φ | ∀ x ∈ F, RCLike.re (φ x) ≤ 1}

end FunctionalAnalysis.BanachSpaceWanted
