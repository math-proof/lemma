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
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part33
/-!
# The strengthened Fleischner theorem

This file proves the vertex-rooted form of Fleischner's theorem: the square has a Hamiltonian
cycle whose two edges at a prescribed vertex are edges of the original graph.

The proof-specific component, trail, transition, Euler-circuit, and marking constructions are
private to this module.
-/

/-! ## CycleComplement -/


namespace SimpleGraph

theorem MarkedNoBacktrack.tail {V : Type*} {a : V × Bool}
    {l : List (V × Bool)} (h : MarkedNoBacktrack (a :: l)) :
    MarkedNoBacktrack l := by
  cases l with
  | nil => trivial
  | cons b l =>
      cases l with
      | nil => trivial
      | cons c l => exact h.2

/-- Removing isolated marked occurrences from a compatible chain leaves a chain in the graph
square. -/
theorem MarkedSquareStep.isChain_unmarkedVertices {V : Type*} {G : SimpleGraph V}
    {l : List (V × Bool)} (hl : l.IsChain (MarkedSquareStep G))
    (hn : MarkedNoBacktrack l) :
    (unmarkedVertices l).IsChain G.square.Adj := by
  induction l with
  | nil => simp [unmarkedVertices]
  | cons a l ih =>
      cases a with
      | mk u marked =>
          cases marked with
          | false =>
              cases l with
              | nil => simp [unmarkedVertices]
              | cons b l =>
                  cases b with
                  | mk v marked' =>
                      have hparts := List.isChain_cons_cons.mp hl
                      cases marked' with
                      | false =>
                          rw [unmarkedVertices, unmarkedVertices]
                          apply List.isChain_cons_cons.mpr
                          exact ⟨hparts.1, ih hparts.2 hn.tail⟩
                      | true =>
                          cases l with
                          | nil => simp [unmarkedVertices]
                          | cons d l =>
                              cases d with
                              | mk w marked'' =>
                                  have hparts' := List.isChain_cons_cons.mp hparts.2
                                  cases marked'' with
                                  | false =>
                                      rw [unmarkedVertices, unmarkedVertices,
                                        unmarkedVertices]
                                      apply List.isChain_cons_cons.mpr
                                      refine ⟨⟨hn.1 rfl,
                                        Or.inr ⟨v, hparts.1, hparts'.1⟩⟩, ?_⟩
                                      exact ih hparts.2 hn.tail
                                  | true =>
                                      exact False.elim (by
                                        simpa [MarkedSquareStep] using hparts'.1)
          | true =>
              rw [unmarkedVertices]
              exact ih (List.IsChain.tail hl) hn.tail

end SimpleGraph

/-! ## EulerCircuitMarking -/

namespace SimpleGraph

namespace EdgeIndexedMultigraph

namespace CyclicCircuit

universe u v

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)

variable (C : M.CyclicCircuit)

theorem unmarkedVertices_map_positions (marked : Fin C.size → Bool)
    (positions : List (Fin C.size)) :
    unmarkedVertices
        (positions.map fun i ↦ (C.vertex i, marked i)) =
      positions.filterMap (C.keptVertex M marked) := by
  induction positions with
  | nil => rfl
  | cons i positions ih =>
      cases hi : marked i <;> simp [unmarkedVertices, keptVertex, hi, ih]

theorem unmarkedVertices_append {l₁ l₂ : List (V × Bool)} :
    unmarkedVertices (l₁ ++ l₂) =
      unmarkedVertices l₁ ++ unmarkedVertices l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a l₁ ih =>
      rcases a with ⟨a, marked⟩
      cases marked <;> simp [unmarkedVertices, ih]

/-- Removing marked entries from the closed marked circuit gives its kept vertex listing. -/
theorem unmarkedVertices_markedVertexListing (start : Fin C.size)
    (marked : Fin C.size → Bool) (hstart : marked start = false) :
    unmarkedVertices (C.markedVertexListing M start marked) =
      C.keptVertexListing M start marked := by
  rw [C.markedVertexListing_eq M start marked, unmarkedVertices_append,
    unmarkedVertices_map_positions, keptVertexListing, keptCoreVertices]
  simp [unmarkedVertices, hstart]

end CyclicCircuit
end EdgeIndexedMultigraph
end SimpleGraph
