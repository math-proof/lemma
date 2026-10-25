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
import Theorem.Topology.Homotopy.BorsukUlam.Part2


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## Gap lemma (pure finset combinatorics) -/

/-- Comparable extensions of a chain of subsets: members of the powerset
missing from `C` but comparable with all of `C`. -/
def bu_tkExt {α : Type*} [DecidableEq α] (C : Finset (Finset α))
    (X : Finset α) : Finset (Finset α) :=
  X.powerset.filter fun M => M ∉ C ∧ ∀ A ∈ C, A ⊆ M ∨ M ⊆ A

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
