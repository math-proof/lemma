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
public import Theorem.Analysis.Calculus.Blumberg.Part3

@[expose] public section

section

namespace MetaMathlibExt

-- Dyadic open intervals and dyadic rationals.
def blumDyI (m : ℕ) (a : ℤ) : Set ℝ :=
  Set.Ioo ((a : ℝ) / 2 ^ m) (((a : ℝ) + 1) / 2 ^ m)

def blumDyadic : Set ℝ :=
  {x : ℝ | ∃ m : ℕ, ∃ a : ℤ, x = (a : ℝ) / 2 ^ m}

end MetaMathlibExt
end
