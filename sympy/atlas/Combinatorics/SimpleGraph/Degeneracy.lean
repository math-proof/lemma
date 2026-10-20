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

/-- Increasing the degree bound preserves degeneracy on a vertex set. -/
theorem IsDegenerateOn.mono [Finite V] (h : G.IsDegenerateOn U k) (hkl : k ≤ l) :
    G.IsDegenerateOn U l := by
  intro W hWne hWU
  obtain ⟨v, hvW, hv⟩ := h W hWne hWU
  exact ⟨v, hvW, hv.trans hkl⟩

/-- Restricting the vertex set preserves degeneracy. -/
theorem IsDegenerateOn.of_subset [Finite V] (h : G.IsDegenerateOn U k) (hTU : T ⊆ U) :
    G.IsDegenerateOn T k := by
  intro W hWne hWT
  exact h W hWne (hWT.trans hTU)

/-- A degenerate graph is degenerate on every subset of its vertices. -/
theorem IsDegenerate.isDegenerateOn [Finite V] (h : G.IsDegenerate k) (U : Set V) :
    G.IsDegenerateOn U k :=
  h.of_subset (Set.subset_univ U)

end SimpleGraph
