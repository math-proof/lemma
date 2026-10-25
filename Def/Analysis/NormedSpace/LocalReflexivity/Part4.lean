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
import Theorem.Analysis.NormedSpace.LocalReflexivity.Part4


namespace FunctionalAnalysis.LocalReflexivityWanted

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable section

/-- The key functional of N5: evaluation at `(1, 0)` plus the `b`-weighted
coordinate functionals. -/
noncomputable def plr_B {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p : ℕ}
    (b : Fin p → StrongDual 𝕜 (StrongDual 𝕜 E))
    (psi : (𝕜 × (Fin p → E)) →L[𝕜] 𝕜) : 𝕜 :=
  psi (1, 0) + ∑ j, b j ((psi.comp ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
    (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) : StrongDual 𝕜 E)

end
end FunctionalAnalysis.LocalReflexivityWanted
