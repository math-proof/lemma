module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
public import Mathlib.Topology.Separation.CompletelyRegular
public import Def.Analysis.NormedSpace.Geometric.Part8


public section

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
