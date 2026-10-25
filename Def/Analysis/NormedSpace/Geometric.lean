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


section

open Set

namespace FunctionalAnalysis.GeometricWanted

/-! ### Step 1–2: the canonical isometry `E →ₗᵢ C(B_{E*}, ℝ)` (Hahn–Banach + Banach–Alaoglu). -/

/-- The closed unit ball of the dual space, seen inside the weak-* dual `WeakDual ℝ E`. -/
def dualBall (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Set (WeakDual ℝ E) :=
  WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1

end FunctionalAnalysis.GeometricWanted
end
