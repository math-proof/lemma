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
import Theorem.Analysis.NormedSpace.Geometric.Part2


section

open Set

namespace FunctionalAnalysis.GeometricWanted

/-- Evaluation `φ ↦ φ x` as a continuous function on the (compact) dual ball. -/
noncomputable def evalCM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    C(dualBall E, ℝ) :=
  ⟨fun φ => (φ : WeakDual ℝ E) x, (WeakDual.eval_continuous x).comp continuous_subtype_val⟩

end FunctionalAnalysis.GeometricWanted
end
