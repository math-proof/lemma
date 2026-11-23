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
public import Def.Analysis.NormedSpace.Geometric.Part2

@[expose] public section

section

open Set

namespace FunctionalAnalysis.GeometricWanted

@[simp] theorem evalCM_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (φ : dualBall E) : evalCM x φ = (φ : WeakDual ℝ E) x := rfl

end FunctionalAnalysis.GeometricWanted
end
