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
import Def.Analysis.NormedSpace.Geometric.Part5


section

open Set

namespace FunctionalAnalysis.GeometricWanted

theorem Fext_mem (f : C(cantorSet, ℝ)) {s : ℝ} (h : s ∈ cantorSet) :
    Fext f s = f ⟨s, h⟩ := dite_eq_left h

end FunctionalAnalysis.GeometricWanted
end
