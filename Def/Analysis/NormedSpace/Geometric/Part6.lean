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
public import Theorem.Analysis.NormedSpace.Geometric.Part6


public section

section

open Set

namespace FunctionalAnalysis.GeometricWanted

noncomputable def frac (y : ℝ) : ℝ :=
  if hi y = lo y then 0 else (y - lo y) / (hi y - lo y)

noncomputable def gval (f : C(cantorSet, ℝ)) (y : ℝ) : ℝ :=
  Fext f (lo y) + (Fext f (hi y) - Fext f (lo y)) * frac y

end FunctionalAnalysis.GeometricWanted
end
