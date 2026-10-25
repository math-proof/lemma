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
import Theorem.Topology.Homotopy.BorsukUlam


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## Moved-set normal form -/

/-- Moved set: coordinates where `z` differs from the bottom `b`. -/
def bu_tkMv {n : ℕ} (b z : Fin n → ℤ) : Finset (Fin n) :=
  Finset.univ.filter fun i => z i ≠ b i

/-- Point with moved set `M`: take `t` on `M`, `b` off `M`. -/
def bu_tkPt {n : ℕ} (b t : Fin n → ℤ) (M : Finset (Fin n)) :
    Fin n → ℤ :=
  fun i => if i ∈ M then t i else b i

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
