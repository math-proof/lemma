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
public import Theorem.Analysis.NormedSpace.LocalReflexivity.Part3

@[expose] public section

namespace FunctionalAnalysis.LocalReflexivityWanted

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable section

/-- The homogenized upper-bound map of N5: `(t, y)` goes to
`t • a + Σ c • y` at each net point. -/
noncomputable def plr_L {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜) :
    (𝕜 × (Fin p → E)) →L[𝕜] (ι → E) :=
  (ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.id 𝕜 𝕜).smulRight (a k)).comp
      (ContinuousLinearMap.fst 𝕜 𝕜 (Fin p → E))
    + (ContinuousLinearMap.pi fun k =>
      ∑ j, (c k j) • ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.snd 𝕜 𝕜 (Fin p → E))

/-- The homogenized equation map of N5. -/
noncomputable def plr_Phi {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E) :
    (𝕜 × (Fin p → E)) →L[𝕜]
      (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) :=
  (ContinuousLinearMap.fst 𝕜 𝕜 (Fin p → E)).prod
    ((ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
        ((f i).comp (ContinuousLinearMap.proj j)).comp
          (ContinuousLinearMap.snd 𝕜 𝕜 (Fin p → E))).prod
      (ContinuousLinearMap.pi fun k =>
        (g k).comp ((ContinuousLinearMap.proj k).comp (plr_L a c))))

/-- The target point of N5. -/
def plr_w {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {p q : ℕ} {ι : Type*}
    (b : Fin p → StrongDual 𝕜 (StrongDual 𝕜 E))
    (f : Fin q → StrongDual 𝕜 E)
    (m : ι → StrongDual 𝕜 (StrongDual 𝕜 E))
    (g : ι → StrongDual 𝕜 E) :
    𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜) :=
  (1, (fun i j => b j (f i)), (fun k => m k (g k)))

end
end FunctionalAnalysis.LocalReflexivityWanted
