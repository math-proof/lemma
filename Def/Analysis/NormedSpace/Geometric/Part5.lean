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
public import Theorem.Analysis.NormedSpace.Geometric.Part5


public section

section

open Set

namespace FunctionalAnalysis.GeometricWanted

open Classical in
/-- `f` extended by `0` off the Cantor set; used only at Cantor points. -/
noncomputable def Fext (f : C(cantorSet, ℝ)) (s : ℝ) : ℝ :=
  if h : s ∈ cantorSet then f ⟨s, h⟩ else 0

end FunctionalAnalysis.GeometricWanted
end
