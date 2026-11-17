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
public import Theorem.Analysis.Calculus.KolmogorovSuperposition
@[expose] public section

open scoped BoundedContinuousFunction


/-- The unit interval as a type. -/
abbrev ksI : Type := Set.Icc (0 : ℝ) 1

/-- The cube `I ^ n`. -/
abbrev ksX (n : ℕ) : Type := Fin n → ksI

/-- The space of inner-function families. -/
abbrev ksPsi (n : ℕ) : Type := Fin (2 * n + 1) → Fin n → C(ksI, ℝ)

