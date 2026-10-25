/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Def.Combinatorics.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.Contraction
import Lemma.SimpleGraph.EdgeIndexedMultigraph
import Lemma.SimpleGraph.Riha
import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
import Theorem.Combinatorics.SimpleGraph.Contraction.Part3
import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
import Def.Combinatorics.SimpleGraph.Riha
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.ZMod.Basic
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part13
/-!
# The strengthened Fleischner theorem

This file proves the vertex-rooted form of Fleischner's theorem: the square has a Hamiltonian
cycle whose two edges at a prescribed vertex are edges of the original graph.

The proof-specific component, trail, transition, Euler-circuit, and marking constructions are
private to this module.
-/

/-! ## CycleComplement -/


namespace SimpleGraph

namespace Walk

variable {V : Type*} {G : SimpleGraph V} {x : V}

theorem cycleCopyIncidence_leftInverse {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    Function.LeftInverse (cycleCopyIncidenceFrom hc q i)
      (cycleCopyIncidenceTo hc q i) := by
  rintro ⟨⟨j, k⟩, he⟩
  by_cases hji : j = i
  · subst j
    simp [cycleCopyIncidenceTo, cycleCopyIncidenceFrom]
  · have hjp : j = i - 1 :=
      (cycleCopyMultigraph_inc_getVert_iff hc q i ⟨j, k⟩).mp he |>.resolve_left hji
    subst j
    simp [cycleCopyIncidenceTo, cycleCopyIncidenceFrom, hc.sub_one_ne i]

theorem cycleCopyIncidence_rightInverse {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    Function.RightInverse (cycleCopyIncidenceFrom hc q i)
      (cycleCopyIncidenceTo hc q i) := by
  intro e
  cases e with
  | inl k =>
      simp [cycleCopyIncidenceTo, cycleCopyIncidenceFrom, hc.sub_one_ne i]
  | inr k =>
      simp [cycleCopyIncidenceTo, cycleCopyIncidenceFrom]

end Walk
end SimpleGraph
