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
import Structure.Combinatorics.SimpleGraph.FleischnerStrong.Part9
/-!
# The strengthened Fleischner theorem

This file proves the vertex-rooted form of Fleischner's theorem: the square has a Hamiltonian
cycle whose two edges at a prescribed vertex are edges of the original graph.

The proof-specific component, trail, transition, Euler-circuit, and marking constructions are
private to this module.
-/

/-! ## CycleComplement -/


namespace SimpleGraph

namespace EdgeIndexedMultigraph

namespace CyclicCircuit

universe u v

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)

variable (C : M.CyclicCircuit)

/-- Local edge conditions package a marking into the data needed for square shortcutting. -/
noncomputable def SquareMarking.ofLocal [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) (start : Fin C.size)
    (marked : Fin C.size → Bool) (hroot : C.vertex start = root)
    (hstart : marked start = false)
    (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false)
    (hedge : ∀ i, marked i = false ∨
      marked (cyclicNext C.size C.size_pos i) = false)
    (hsquare : ∀ i, G.square.Adj (C.vertex i)
      (C.vertex (cyclicNext C.size C.size_pos i)))
    (horiginal : ∀ i, marked i = true ∨
      marked (cyclicNext C.size C.size_pos i) = true →
        G.Adj (C.vertex i) (C.vertex (cyclicNext C.size C.size_pos i)))
    (hnext : marked (cyclicNext C.size C.size_pos start) = false)
    (hprev : marked (cyclicPrev C.size C.size_pos start) = false)
    (hnextAdj : G.Adj root
      (C.vertex (cyclicNext C.size C.size_pos start)))
    (hprevAdj : G.Adj
      (C.vertex (cyclicPrev C.size C.size_pos start)) root)
    (hcard : 3 ≤ Fintype.card V) : C.SquareMarking M G root := by
  classical
  have hsize := C.three_le_size_of_unique_unmarked M marked hunique hcard
  refine {
    start := start
    root_start := hroot
    marked := marked
    start_unmarked := hstart
    unique_unmarked := hunique
    two_le_size := by omega
    three_le_card := hcard
    marked_square_chain := ?_
    no_backtrack := C.markedVertexListing_noBacktrack M start marked
      hunique hedge hcard
    next_unmarked := hnext
    prev_unmarked := hprev
    next_adj := hnextAdj
    prev_adj := hprevAdj }
  apply C.markedVertexListing_isChain M
  intro i
  let j := cyclicNext C.size C.size_pos i
  cases hi : marked i <;> cases hj : marked j
  · simpa [MarkedSquareStep, j, hi, hj] using hsquare i
  · simpa [MarkedSquareStep, j, hi, hj] using
      horiginal i (Or.inr hj)
  · simpa [MarkedSquareStep, j, hi, hj] using
      horiginal i (Or.inl hi)
  · rcases hedge i with h | h
    · simp [hi] at h
    · simp [j, hj] at h

/-- A compatible square marking produces the rooted cyclic listing obtained by lifting every
marked pass. -/
noncomputable def SquareMarking.toStrongSquareCycleListing
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {root : V}
    (K : C.SquareMarking M G root) : G.StrongSquareCycleListing root := by
  classical
  let l := C.keptVertexListing M K.start K.marked
  let frontExists := C.keptVertexListing_eq_root_next M K.start K.marked
    K.two_le_size K.start_unmarked K.next_unmarked
  let middle := Classical.choose frontExists
  have hfront := Classical.choose_spec frontExists
  let backExists := C.keptVertexListing_eq_prev_root M K.start K.marked
    K.start_unmarked K.prev_unmarked
  let initial := Classical.choose backExists
  have hback := Classical.choose_spec backExists
  have hfront' : l = C.vertex K.start ::
      C.vertex (cyclicNext C.size C.size_pos K.start) ::
        middle ++ [C.vertex K.start] := by
    simpa only [l, middle] using hfront
  have hback' : l = initial ++
      [C.vertex (cyclicPrev C.size C.size_pos K.start), C.vertex K.start] := by
    simpa only [l, initial] using hback
  have htailNodup : l.tail.Nodup :=
    C.keptVertexListing_tail_nodup M K.start K.marked
      K.start_unmarked K.unique_unmarked
  have hmem : ∀ z, z ∈ l.tail :=
    C.mem_tail_keptVertexListing M K.start K.marked
      K.start_unmarked K.unique_unmarked
  have htailFinset : l.tail.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro z
    exact List.mem_toFinset.mpr (hmem z)
  have htailLength : l.tail.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup htailNodup, htailFinset,
      Finset.card_univ]
  have hlength : l.length = l.tail.length + 1 := by
    rw [hfront']
    simp
  have hcard : 3 ≤ Fintype.card V := K.three_le_card
  have hfour : 4 ≤ l.length := by omega
  have hchain : l.IsChain G.square.Adj := by
    have h := MarkedSquareStep.isChain_unmarkedVertices
      K.marked_square_chain K.no_backtrack
    rw [C.unmarkedVertices_markedVertexListing M K.start K.marked
      K.start_unmarked] at h
    exact h
  refine {
    vertices := l
    first := C.vertex (cyclicNext C.size C.size_pos K.start)
    last := C.vertex (cyclicPrev C.size C.size_pos K.start)
    frontRest := middle ++ [C.vertex K.start]
    backRest := initial
    front_shape := by simpa [K.root_start] using hfront'
    back_shape := by simpa only [K.root_start] using hback'
    four_le_length := hfour
    square_chain := hchain
    tail_nodup := htailNodup
    mem_tail := hmem
    first_adj := K.next_adj
    last_adj := K.prev_adj }

end CyclicCircuit

end EdgeIndexedMultigraph

end SimpleGraph

namespace SimpleGraph

namespace Walk

/-- The cycle-edge index anchored at a vertex when the two arcs from zero to `k` are
oriented away from zero. -/
def splitCycleAnchorIndex {n : ℕ} [NeZero n] (k i : Fin n) : Fin n :=
  if i = 0 then 0 else if i.val ≤ k.val then i - 1 else i

/-- Original cycle edges used as anchors for the split transition system. -/
def splitCycleAnchor (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k i : Fin c.length) : c.AugmentedTrailEdge cover q :=
  c.augmentedOriginalEdge cover q (splitCycleAnchorIndex k i)

end Walk
end SimpleGraph
