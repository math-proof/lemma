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
import Theorem.Analysis.NormedSpace.LocalReflexivity.Part3


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
