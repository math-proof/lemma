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
public import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part20


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
