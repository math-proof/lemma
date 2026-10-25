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
import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part20
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

variable (C : M.CyclicCircuit)

/-- The edge entering a cyclic position. -/
def incoming (i : Fin C.size) : E :=
  C.edge (cyclicPrev C.size C.size_pos i)

/-- A pass is kept when its designated anchor is one of its two incident tour edges. -/
def Keeps (anchor : V → E) (i : Fin C.size) : Prop :=
  incoming M C i = anchor (C.vertex i) ∨ C.edge i = anchor (C.vertex i)

/-- Mark every pass except the pass containing the designated anchor edge. -/
noncomputable def anchorMarked (anchor : V → E) (i : Fin C.size) : Bool :=
  by
    classical
    exact decide (¬Keeps M C anchor i)

end CyclicCircuit

end EdgeIndexedMultigraph

end SimpleGraph

namespace SimpleGraph

/-- Consecutive tagged vertices are compatible with shortcutting exactly the marked ones. -/
def MarkedSquareStep {V : Type*} (G : SimpleGraph V)
    (a b : V × Bool) : Prop :=
  match a.2, b.2 with
  | false, false => G.square.Adj a.1 b.1
  | false, true => G.Adj a.1 b.1
  | true, false => G.Adj a.1 b.1
  | true, true => False

/-- Remove marked occurrences and forget the tags. -/
def unmarkedVertices {V : Type*} : List (V × Bool) → List V
  | [] => []
  | (v, false) :: l => v :: unmarkedVertices l
  | (_, true) :: l => unmarkedVertices l

/-- A marked middle occurrence never has equal neighbors. -/
def MarkedNoBacktrack {V : Type*} : List (V × Bool) → Prop
  | a :: b :: c :: l => (b.2 = true → a.1 ≠ c.1) ∧ MarkedNoBacktrack (b :: c :: l)
  | _ => True

end SimpleGraph
