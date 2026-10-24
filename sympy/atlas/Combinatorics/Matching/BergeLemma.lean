/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/BergeLemma.lean -/

import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Lattice.Nat

open scoped symmDiff

private def mateSet {V : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq (Sym2 V)] (M : Finset (Sym2 V)) (v : V) : Finset V :=
  Finset.univ.filter (fun w => s(v, w) ∈ M)

/-- A `Finset` matching as a `SimpleGraph.Subgraph`: vertices are the covered
vertices, adjacency is edge membership. -/
private def subgraphOfFinset {V : Type*} (G : SimpleGraph V)
    (M : Finset (Sym2 V)) (hG : ∀ e ∈ M, e ∈ G.edgeSet) : G.Subgraph where
  verts := {v | ∃ e ∈ M, v ∈ e}
  Adj v w := s(v, w) ∈ M
  adj_sub {v w} h := (SimpleGraph.mem_edgeSet G).mp (hG _ h)
  edge_vert {v w} h := ⟨s(v, w), h, Sym2.mem_mk_left v w⟩
  symm := ⟨fun a b h => by rwa [Sym2.eq_swap]⟩

/-- A `Subgraph`'s edge set as a `Finset`, for `Finite` vertex types. -/
private noncomputable def finsetOfSubgraph {V : Type*} [Finite V]
    (G : SimpleGraph V) (M : G.Subgraph) : Finset (Sym2 V) :=
  haveI : Finite (Sym2 V) := Quot.finite _
  (Set.finite_univ.subset (Set.subset_univ M.edgeSet)).toFinset
section
namespace MetaMathlibExt
end MetaMathlibExt
end
