/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.HeineCantor
import Theorem.Topology.Homotopy.BorsukUlam.Part10


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## The no-zero contradiction -/

/-- Grid points scaled into the unit cube. -/
noncomputable def buPt {n : ℕ} (m : ℕ) (z : Fin n → ℤ) : Fin n → ℝ :=
  fun i => ((z i : ℤ) : ℝ) / (m : ℝ)

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
