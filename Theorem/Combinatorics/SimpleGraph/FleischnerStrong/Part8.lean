module
public import Def.Combinatorics.SimpleGraph.StrongSquareCycle
public import Theorem.SimpleGraph.StrongSquareCycle
public import Theorem.SimpleGraph.VertexConnectivity
public import Theorem.SimpleGraph.Contraction
public import Theorem.SimpleGraph.EdgeIndexedMultigraph
public import Theorem.SimpleGraph.Riha
public import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
public import Theorem.Combinatorics.SimpleGraph.Contraction.Part3
public import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
public import Def.Combinatorics.SimpleGraph.Riha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.ZMod.Basic
public import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part13


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
