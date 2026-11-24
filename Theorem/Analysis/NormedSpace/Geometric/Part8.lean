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
public import Def.Analysis.NormedSpace.Geometric.Part7


public section

section

open Set

namespace FunctionalAnalysis.GeometricWanted

@[simp] theorem gvalCM_apply (f : C(cantorSet, ℝ)) (y : Icc (0 : ℝ) 1) :
    gvalCM f y = gval f y.1 := rfl

theorem Fext_add (f g : C(cantorSet, ℝ)) (s : ℝ) :
    Fext (f + g) s = Fext f s + Fext g s := by unfold Fext; split_ifs with h <;> simp

theorem Fext_smul (c : ℝ) (f : C(cantorSet, ℝ)) (s : ℝ) :
    Fext (c • f) s = c * Fext f s := by unfold Fext; split_ifs with h <;> simp

end FunctionalAnalysis.GeometricWanted
end
