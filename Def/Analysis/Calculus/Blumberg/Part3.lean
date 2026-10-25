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
import Theorem.Analysis.Calculus.Blumberg.Part3


section

namespace MetaMathlibExt

-- Dyadic open intervals and dyadic rationals.
def blumDyI (m : ℕ) (a : ℤ) : Set ℝ :=
  Set.Ioo ((a : ℝ) / 2 ^ m) (((a : ℝ) + 1) / 2 ^ m)

def blumDyadic : Set ℝ :=
  {x : ℝ | ∃ m : ℕ, ∃ a : ℤ, x = (a : ℝ) / 2 ^ m}

end MetaMathlibExt
end
