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
import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part19
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

namespace IndexedWalk

/-- An indexed Euler circuit with at least one edge gives a cyclic edge-position encoding. -/
noncomputable def toCyclicCircuit [Nonempty E] {x : V}
    (p : M.IndexedWalk x x) (hp : p.IsEulerian) : M.CyclicCircuit := by
  classical
  have hne : p.edges ≠ [] := by
    let e : E := Classical.choice (inferInstance : Nonempty E)
    exact fun h ↦ by simpa [h] using hp.2 e
  refine {
    size := p.edges.length
    size_pos := List.length_pos_of_ne_nil hne
    vertex := fun i ↦ p.toWalk.getVert i.val
    edge := p.edges.get
    ends_edge := ?_
    edge_bijective := ?_ }
  · intro i
    have hi : i.val < p.toWalk.edges.length := by
      rw [p.toWalk.length_edges, p.length_toWalk]
      exact i.isLt
    have hedge := p.toWalk.getElem_edges hi
    have hmap : p.toWalk.edges[i.val]'hi = M.ends (p.edges[i.val]'i.isLt) := by
      simp only [p.edges_toWalk, List.getElem_map]
    calc
      M.ends (p.edges.get i) = p.toWalk.edges.get ⟨i.val, hi⟩ := hmap.symm
      _ = s(p.toWalk.getVert i.val, p.toWalk.getVert (i.val + 1)) := by
        simpa using hedge
      _ = s(p.toWalk.getVert i.val,
          p.toWalk.getVert
            (cyclicNext p.edges.length (List.length_pos_of_ne_nil hne) i).val) :=
        congrArg (s(p.toWalk.getVert i.val, ·)) (getVert_succ_fin M p hne i)
  · constructor
    · exact hp.1.injective_get
    · intro e
      exact List.mem_iff_get.mp (hp.2 e)

end IndexedWalk

namespace CyclicCircuit

variable (C : M.CyclicCircuit)

/-- Add an offset to a cyclic position, using the circuit size as modulus. -/
def rotatedPosition (start i : Fin C.size) : Fin C.size :=
  let _ : NeZero C.size := ⟨Nat.ne_of_gt C.size_pos⟩
  start + i

/-- All cyclic positions, starting at a prescribed position. -/
def rotatedPositions (start : Fin C.size) : List (Fin C.size) :=
  List.ofFn fun i ↦ C.rotatedPosition M start i

/-- A cyclic position list with the initial position repeated at the end. -/
def closedRotatedPosition (start : Fin C.size) (i : Fin (C.size + 1)) :
    Fin C.size :=
  if hi : i.val < C.size then C.rotatedPosition M start ⟨i.val, hi⟩ else start

/-- Vertices and pass marks in cyclic order, with the initial entry repeated at the end. -/
def markedVertexListing (start : Fin C.size) (marked : Fin C.size → Bool) :
    List (V × Bool) :=
  List.ofFn fun i ↦
    let j := C.closedRotatedPosition M start i
    (C.vertex j, marked j)

/-- Keep an unmarked cyclic occurrence and discard a marked occurrence. -/
def keptVertex (marked : Fin C.size → Bool) (i : Fin C.size) : Option V :=
  if marked i then none else some (C.vertex i)

/-- The unmarked vertices in one nonrepeating turn around the circuit. -/
def keptCoreVertices (start : Fin C.size) (marked : Fin C.size → Bool) :
    List V :=
  (C.rotatedPositions M start).filterMap (C.keptVertex M marked)

/-- The unmarked cyclic listing, closed by repeating its initial vertex. -/
def keptVertexListing (start : Fin C.size) (marked : Fin C.size → Bool) :
    List V :=
  C.keptCoreVertices M start marked ++ [C.vertex start]

end CyclicCircuit
end EdgeIndexedMultigraph
end SimpleGraph
