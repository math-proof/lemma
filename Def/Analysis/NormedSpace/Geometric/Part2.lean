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
public import Theorem.Analysis.NormedSpace.Geometric.Part2

@[expose] public section

section

open Set

namespace FunctionalAnalysis.GeometricWanted

/-- Evaluation `φ ↦ φ x` as a continuous function on the (compact) dual ball. -/
noncomputable def evalCM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    C(dualBall E, ℝ) :=
  ⟨fun φ => (φ : WeakDual ℝ E) x, (WeakDual.eval_continuous x).comp continuous_subtype_val⟩

end FunctionalAnalysis.GeometricWanted
end
