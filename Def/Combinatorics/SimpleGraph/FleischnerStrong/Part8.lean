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
import Instance.Combinatorics.SimpleGraph.FleischnerStrong
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

universe u

variable {V : Type u} {G : SimpleGraph V} {x : V}

/-- The indexed multigraph formed by the cycle and all outside-component trail covers. -/
noncomputable def trailSystemMultigraph (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :
    EdgeIndexedMultigraph V (c.TrailSystemEdge cover) where
  ends
    | Sum.inl i => s(c.getVert i.down, c.getVert (i.down + 1))
    | Sum.inr e => (cover e.1).multigraph.ends e.2
  loopless := by
    intro e v he
    cases e with
    | inl i =>
        have hadj := c.adj_getVert_succ i.down.isLt
        have hedge : s(c.getVert i.down, c.getVert (i.down + 1)) ∈ G.edgeSet :=
          G.mem_edgeSet.mpr hadj
        change s(c.getVert i.down, c.getVert (i.down + 1)) = s(v, v) at he
        rw [he] at hedge
        exact G.loopless.irrefl v (G.mem_edgeSet.mp hedge)
    | inr e => exact (cover e.1).multigraph.loopless e.2 v he

def outsideComponent (c : G.Walk x x) {v : V} (hv : v ∉ c.support) :
    c.outsideGraph.ConnectedComponent :=
  c.outsideGraph.connectedComponentMk ⟨v, hv⟩

end Walk
end SimpleGraph
