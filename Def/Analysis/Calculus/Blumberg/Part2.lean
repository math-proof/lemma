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
public import Theorem.Analysis.Calculus.Blumberg.Part2

@[expose] public section

section

namespace MetaMathlibExt

-- Good points: category version of continuity points.
def blumGood (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ V : Set ℝ, IsOpen V → V.Nonempty →
    V ⊆ Metric.ball x δ → ¬ IsMeagre ({y | dist (f y) (f x) < ε} ∩ V)

end MetaMathlibExt
end
