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
import Theorem.Analysis.NormedSpace.Geometric.Part7


section

open Set

namespace FunctionalAnalysis.GeometricWanted

noncomputable def gvalCM (f : C(cantorSet, ℝ)) : C(Icc (0:ℝ) 1, ℝ) :=
  ⟨fun y => gval f y.1, (gval_continuousOn f).domRestrict⟩

end FunctionalAnalysis.GeometricWanted
end
