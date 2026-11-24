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
public import Theorem.Analysis.NormedSpace.Geometric.Part4


public section

section

open Set

namespace FunctionalAnalysis.GeometricWanted

noncomputable def lo (y : ℝ) : ℝ := sSup (cantorSet ∩ Iic y)

noncomputable def hi (y : ℝ) : ℝ := sInf (cantorSet ∩ Ici y)

end FunctionalAnalysis.GeometricWanted
end
