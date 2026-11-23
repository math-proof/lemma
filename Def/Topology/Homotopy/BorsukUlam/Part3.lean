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
public import Theorem.Topology.Homotopy.BorsukUlam.Part2

@[expose] public section

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## Gap lemma (pure finset combinatorics) -/

/-- Comparable extensions of a chain of subsets: members of the powerset
missing from `C` but comparable with all of `C`. -/
def bu_tkExt {α : Type*} [DecidableEq α] (C : Finset (Finset α))
    (X : Finset α) : Finset (Finset α) :=
  X.powerset.filter fun M => M ∉ C ∧ ∀ A ∈ C, A ⊆ M ∨ M ⊆ A

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
