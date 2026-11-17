/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/BergeLemma.lean -/

module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.Lattice.Nat

@[expose] public section

open scoped symmDiff


def mateSet {V : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq (Sym2 V)] (M : Finset (Sym2 V)) (v : V) : Finset V :=
  Finset.univ.filter (fun w => s(v, w) ∈ M)

/-- A `Finset` matching as a `SimpleGraph.Subgraph`: vertices are the covered
vertices, adjacency is edge membership. -/
def subgraphOfFinset {V : Type*} (G : SimpleGraph V)
    (M : Finset (Sym2 V)) (hG : ∀ e ∈ M, e ∈ G.edgeSet) : G.Subgraph where
  verts := {v | ∃ e ∈ M, v ∈ e}
  Adj v w := s(v, w) ∈ M
  adj_sub {v w} h := (SimpleGraph.mem_edgeSet G).mp (hG _ h)
  edge_vert {v w} h := ⟨s(v, w), h, Sym2.mem_mk_left v w⟩
  symm := ⟨fun a b h => by rwa [Sym2.eq_swap]⟩

/-- A `Subgraph`'s edge set as a `Finset`, for `Finite` vertex types. -/
noncomputable def finsetOfSubgraph {V : Type*} [Finite V]
    (G : SimpleGraph V) (M : G.Subgraph) : Finset (Sym2 V) :=
  haveI : Finite (Sym2 V) := Quot.finite _
  (Set.finite_univ.subset (Set.subset_univ M.edgeSet)).toFinset

