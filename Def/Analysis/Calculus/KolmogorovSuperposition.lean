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

@[expose] public section

open scoped BoundedContinuousFunction


noncomputable def stepRamp (c a : ℕ → ℝ) (K : ℕ) (z : ℝ) : ℝ :=
  c 0 + ∑ i ∈ Finset.range K, (c (i + 1) - c i) * min 1 (max 0 (z - a i))

