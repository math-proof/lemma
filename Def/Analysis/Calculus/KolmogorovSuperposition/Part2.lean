/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Abbrev.Analysis.Calculus.KolmogorovSuperposition
open scoped BoundedContinuousFunction


/-- The contraction factor `θ = (2n+1)/(2n+2)`. -/
noncomputable def ksTheta (n : ℕ) : ℝ := (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)

/-- Inner sum of family `q` at `x`. -/
noncomputable def kolmogorovInner (n : ℕ) (ψ : ksPsi n)
    (q : Fin (2 * n + 1)) (x : ksX n) : ℝ :=
  ∑ p, ψ q p (x p)

/-- Superposition operator: `x ↦ ∑ q, g q (inner ψ q x)`. -/
noncomputable def kolmogorovSuperpose (n : ℕ) (ψ : ksPsi n)
    (g : Fin (2 * n + 1) → ℝ →ᵇ ℝ) : C(ksX n, ℝ) where
  toFun x := ∑ q, g q (kolmogorovInner n ψ q x)
  continuous_toFun := by
    apply continuous_finsetSum
    intro q _
    apply Continuous.comp (g q).continuous
    apply continuous_finsetSum
    intro p _
    exact (ψ q p).continuous.comp (continuous_apply p)

/-- Good set of inner families for `f`: those admitting a bounded outer
family `g` with `‖f - T g‖ < θ‖f‖`. -/
noncomputable def kolmogorovGoodSet (n : ℕ) (f : C(ksX n, ℝ)) : Set (ksPsi n) :=
  {ψ | ∃ g : Fin (2 * n + 1) → ℝ →ᵇ ℝ,
    (∀ q, ‖g q‖ ≤ ‖f‖ / ((n : ℝ) + 1))
      ∧ ‖f - kolmogorovSuperpose n ψ g‖ < ksTheta n * ‖f‖}

/-- Left end of gap cell `i` of family `q`, in z-units. -/
noncomputable def ksGap (n : ℕ) (q : Fin (2 * n + 1)) (i : ℕ) : ℝ :=
  (i : ℝ) * (2 * (n : ℝ) + 1) + (q.val : ℝ)

/-- `t` lies in an open gap cell of family `q` at scale `N`. -/
def ksBad (n N : ℕ) (q : Fin (2 * n + 1)) (t : ℝ) : Prop :=
  ∃ m : ℤ, m % ((2 * n + 1 : ℕ) : ℤ) = (q.val : ℤ)
    ∧ (m : ℝ) < (N : ℝ) * t ∧ (N : ℝ) * t < (m : ℝ) + 1

/-- Index of the good interval containing `t` for family `q`. -/
noncomputable def ksIdx (n N : ℕ) (q : Fin (2 * n + 1)) (t : ℝ) : ℕ :=
  ⌊((N : ℝ) * t + 2 * (n : ℝ) - (q.val : ℝ)) / (2 * (n : ℝ) + 1)⌋₊

/-- Left end of good interval `k` of family `q`, clamped into `I`. -/
noncomputable def ksRep (n N : ℕ) (q : Fin (2 * n + 1)) (k : ℕ) : ksI :=
  Set.projIcc 0 1 zero_le_one
    (((k : ℝ) * (2 * (n : ℝ) + 1) + (q.val : ℝ) - 2 * (n : ℝ)) / (N : ℝ))

