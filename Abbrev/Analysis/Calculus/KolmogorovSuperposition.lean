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
import Theorem.Analysis.Calculus.KolmogorovSuperposition
open scoped BoundedContinuousFunction


/-- The unit interval as a type. -/
abbrev ksI : Type := Set.Icc (0 : ℝ) 1

/-- The cube `I ^ n`. -/
abbrev ksX (n : ℕ) : Type := Fin n → ksI

/-- The space of inner-function families. -/
abbrev ksPsi (n : ℕ) : Type := Fin (2 * n + 1) → Fin n → C(ksI, ℝ)

