import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable


section

namespace MetaMathlibExt

-- N1: countable subsets of ℝ are meagre.
theorem blum_isMeagre_of_countable (S : Set ℝ) (hS : S.Countable) :
    IsMeagre S := by
  have hEq : S = ⋃ x ∈ S, ({x} : Set ℝ) := by
    ext y
    simp
  rw [hEq]
  apply isMeagre_biUnion hS
  intro x _
  apply IsNowhereDense.isMeagre
  rw [IsClosed.isNowhereDense_iff isClosed_singleton]
  exact interior_singleton x

end MetaMathlibExt
end
