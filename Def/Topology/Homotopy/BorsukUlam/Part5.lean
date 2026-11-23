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
public import Theorem.Topology.Homotopy.BorsukUlam.Part3

@[expose] public section

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-- Pull `c`: the bottom with coordinate `c` moved one step toward `0`. -/
def bu_tkPull {n : ℕ} (b : Fin n → ℤ) (c : Fin n) : Fin n → ℤ :=
  fun i => if i = c then (if 0 < b c then b c - 1 else b c + 1) else b i

/-- Push `j` up by one. -/
def bu_tkPush {n : ℕ} (t : Fin n → ℤ) (j : Fin n) (s : ℤ) : Fin n → ℤ :=
  fun i => if i = j then t j + s else t i

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
