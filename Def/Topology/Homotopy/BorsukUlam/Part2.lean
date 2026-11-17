/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Theorem.Topology.Homotopy.BorsukUlam

@[expose] public section

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
