/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Degeneracy.lean -/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card

/-!
# Degenerate graphs

A finite graph is `k`-degenerate on a vertex set when every nonempty subset contains a
vertex with at most `k` neighbors in that subset. The unrestricted version takes the
vertex set to be universal.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {U T : Set V} {k l : ℕ}

/-- `G` is `k`-degenerate on `U` if every nonempty subset of `U` contains a
vertex with at most `k` neighbors inside that subset. -/
def IsDegenerateOn {V : Type*} [Finite V] (G : SimpleGraph V) (U : Set V) (k : ℕ) : Prop :=
  ∀ W : Set V, W.Nonempty → W ⊆ U →
    ∃ v ∈ W, (G.neighborSet v ∩ W).ncard ≤ k

/-- A graph is `k`-degenerate if it is `k`-degenerate on its full vertex set. -/
def IsDegenerate {V : Type*} [Finite V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.IsDegenerateOn Set.univ k
end SimpleGraph
