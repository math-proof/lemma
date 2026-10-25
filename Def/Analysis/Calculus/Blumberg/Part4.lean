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
import Theorem.Analysis.Calculus.Blumberg.Part4


section

namespace MetaMathlibExt

-- Labels are `(level, dyadic index, band center, band radius)`.
-- State is `(chosen points, labels)`.
def blumInv (f : ℝ → ℝ) (s : Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ)) :
    Prop :=
  (∀ d ∈ s.1, blumGood f d ∧ d ∉ blumDyadic) ∧
  (∀ ℓ ∈ s.2, ∀ d ∈ s.1, d ∈ blumDyI ℓ.1 ℓ.2.1 →
    dist (f d) ℓ.2.2.1 < ℓ.2.2.2) ∧
  (∀ ℓ ∈ s.2, ∀ ℓ' ∈ s.2, blumDyI ℓ.1 ℓ.2.1 ⊆ blumDyI ℓ'.1 ℓ'.2.1 →
    Metric.ball ℓ.2.2.1 ℓ.2.2.2 ⊆ Metric.ball ℓ'.2.2.1 ℓ'.2.2.2) ∧
  (∀ ℓ ∈ s.2, ∀ V : Set ℝ, IsOpen V → V.Nonempty → V ⊆ blumDyI ℓ.1 ℓ.2.1 →
    ¬ IsMeagre ((f ⁻¹' Metric.ball ℓ.2.2.1 ℓ.2.2.2) ∩ V))

end MetaMathlibExt
end
