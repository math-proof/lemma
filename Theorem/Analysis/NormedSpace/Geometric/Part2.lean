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
public import Instance.Analysis.NormedSpace.Geometric

public section

section

open Set

namespace FunctionalAnalysis.GeometricWanted

theorem mem_dualBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : WeakDual ℝ E} : φ ∈ dualBall E ↔ ‖WeakDual.toStrongDual φ‖ ≤ 1 := by
  simp [dualBall]

end FunctionalAnalysis.GeometricWanted
end
