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
import Theorem.Analysis.NormedSpace.Geometric.Part5


section

open Set

namespace FunctionalAnalysis.GeometricWanted

open Classical in
/-- `f` extended by `0` off the Cantor set; used only at Cantor points. -/
noncomputable def Fext (f : C(cantorSet, ℝ)) (s : ℝ) : ℝ :=
  if h : s ∈ cantorSet then f ⟨s, h⟩ else 0

end FunctionalAnalysis.GeometricWanted
end
