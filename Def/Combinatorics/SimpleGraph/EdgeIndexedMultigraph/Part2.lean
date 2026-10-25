/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Trails
import Lemma.SimpleGraph.EulerCircuit
import Theorem.Combinatorics.SimpleGraph.EdgeIndexedMultigraph
/-!
# Finite edge-indexed multigraphs

Parallel edges are represented by distinct elements of the edge type. The incidence subdivision
turns such a multigraph into a simple bipartite graph and transfers Euler circuits back to an
edge-distinguishing representation.
-/


namespace SimpleGraph

namespace EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)

/-- A vertex is incident with an edge when it belongs to the edge's endpoint pair. -/
def Inc (v : V) (e : E) : Prop :=
  v ∈ M.ends e

/-- The simple graph obtained by forgetting edge multiplicities. -/
def underlying : SimpleGraph V :=
  fromEdgeSet (Set.range M.ends)

namespace IndexedWalk

/-- Forget edge identities in an indexed walk. -/
def toWalk {u v : V} : M.IndexedWalk u v → M.underlying.Walk u v
  | .nil w => .nil
  | .cons e he p => .cons (M.underlying_adj.mpr ⟨e, he⟩) p.toWalk

end IndexedWalk

/-- The number of indexed edges incident with a vertex. -/
noncomputable def degree (v : V) : ℕ :=
  {e | M.Inc v e}.ncard

/-- Disjoint union of two indexed edge sets on the same vertex type. -/
def disjointSum {F : Type*} (N : EdgeIndexedMultigraph V F) :
    EdgeIndexedMultigraph V (E ⊕ F) where
  ends
    | Sum.inl e => M.ends e
    | Sum.inr f => N.ends f
  loopless := by
    intro e v
    cases e with
    | inl e => exact M.loopless e v
    | inr f => exact N.loopless f v

def disjointSumIncidenceEquiv {F : Type*} (N : EdgeIndexedMultigraph V F)
    (v : V) :
    {e : E ⊕ F // (M.disjointSum N).Inc v e} ≃
      {e : E // M.Inc v e} ⊕ {f : F // N.Inc v f} where
  toFun e := by
    rcases e with ⟨e, he⟩
    cases e with
    | inl e => exact Sum.inl ⟨e, he⟩
    | inr f => exact Sum.inr ⟨f, he⟩
  invFun e := by
    cases e with
    | inl e => exact ⟨Sum.inl e.1, e.2⟩
    | inr f => exact ⟨Sum.inr f.1, f.2⟩
  left_inv := by
    rintro ⟨e, he⟩
    cases e <;> rfl
  right_inv := by
    intro e
    cases e <;> rfl

/-- The bipartite simple graph obtained by subdividing every indexed edge once. -/
def incidenceGraph : SimpleGraph (V ⊕ E) where
  Adj a b := match a, b with
    | Sum.inl v, Sum.inr e => M.Inc v e
    | Sum.inr e, Sum.inl v => M.Inc v e
    | _, _ => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> simp_all⟩
  loopless := ⟨by
    intro a
    cases a <;> simp⟩

end EdgeIndexedMultigraph
end SimpleGraph
