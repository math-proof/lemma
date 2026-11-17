/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Contracting
public import Theorem.Analysis.NormedSpace.BrowderKirk

@[expose] public section

section

open Set

namespace FunctionalAnalysis.BrowderKirkWanted

/-- Asymptotic radius of a sequence at a point: `limsup_n ‖u n - x‖`. -/
noncomputable def asympRadius {E : Type*} [NormedAddCommGroup E] (u : ℕ → E) (x : E) : ℝ :=
  Filter.limsup (fun n => ‖u n - x‖) Filter.atTop

end FunctionalAnalysis.BrowderKirkWanted
end
