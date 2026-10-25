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
import Theorem.Topology.Homotopy.BorsukUlam.Part3


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-- Pull `c`: the bottom with coordinate `c` moved one step toward `0`. -/
def bu_tkPull {n : ℕ} (b : Fin n → ℤ) (c : Fin n) : Fin n → ℤ :=
  fun i => if i = c then (if 0 < b c then b c - 1 else b c + 1) else b i

/-- Push `j` up by one. -/
def bu_tkPush {n : ℕ} (t : Fin n → ℤ) (j : Fin n) (s : ℤ) : Fin n → ℤ :=
  fun i => if i = j then t j + s else t i

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
