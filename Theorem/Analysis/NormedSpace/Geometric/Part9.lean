import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
import Mathlib.Topology.Separation.CompletelyRegular
import Def.Analysis.NormedSpace.Geometric.Part8


section

open Set

namespace FunctionalAnalysis.GeometricWanted

/-! ### Assembly. -/

/--
Every separable real Banach space admits a linear isometric embedding with closed range into
`C([0, 1], ℝ)`. Source: S. Banach and S. Mazur 1932 embedding theorem; Banach, Theorie des
operations lineaires; Henson-Michalewski, separable Banach as universal space; Lean states
separable real Banach case with `E →ₗᵢ[ℝ] C(Icc 0 1, ℝ)` and `IsClosed (range)`.

Proves `Wanted` entry `banachMazur_embedding`.
-/
theorem banachMazur_embedding
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ (e : E →ₗᵢ[ℝ] C(Set.Icc (0:ℝ) 1, ℝ)), IsClosed
        (Set.range (e : E → C(Set.Icc (0:ℝ) 1, ℝ))) := by
  obtain ⟨Φf, hΦc, hΦs⟩ := exists_cantor_surjection E
  let Φ : C(cantorSet, dualBall E) := ⟨Φf, hΦc⟩
  refine ⟨extendLI.comp ((precompLI Φ hΦs).comp toCK), ?_⟩
  exact (extendLI.comp ((precompLI Φ hΦs).comp
    toCK)).isometry.isUniformInducing.isComplete_range.isClosed

end FunctionalAnalysis.GeometricWanted
end
