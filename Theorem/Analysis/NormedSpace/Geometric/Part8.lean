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
import Def.Analysis.NormedSpace.Geometric.Part7


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
