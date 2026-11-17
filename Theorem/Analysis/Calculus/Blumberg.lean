module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Data.Int.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.UniformSpace.Uniformizable

public section

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
