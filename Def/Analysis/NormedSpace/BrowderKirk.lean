/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Theorem.Analysis.NormedSpace.BrowderKirk


section

open Set

namespace FunctionalAnalysis.BrowderKirkWanted

/-- Asymptotic radius of a sequence at a point: `limsup_n ‖u n - x‖`. -/
noncomputable def asympRadius {E : Type*} [NormedAddCommGroup E] (u : ℕ → E) (x : E) : ℝ :=
  Filter.limsup (fun n => ‖u n - x‖) Filter.atTop

end FunctionalAnalysis.BrowderKirkWanted
end
