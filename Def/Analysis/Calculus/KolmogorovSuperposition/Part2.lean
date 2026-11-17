/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Bases
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Abbrev.Analysis.Calculus.KolmogorovSuperposition

@[expose] public section

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

