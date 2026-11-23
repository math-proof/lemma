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
public import Theorem.Analysis.Calculus.Blumberg.Part4

@[expose] public section

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
