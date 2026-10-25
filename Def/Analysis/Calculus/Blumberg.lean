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
import Theorem.Analysis.Calculus.Blumberg


section

namespace MetaMathlibExt

-- Category points.
def blumCat (A : Set ℝ) : Set ℝ :=
  {x : ℝ | ∀ U : Set ℝ, IsOpen U → x ∈ U → ¬ IsMeagre (A ∩ U)}

end MetaMathlibExt
end
