/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Trails

import Lemma.SimpleGraph.EulerCircuit
/-!
# Finite edge-indexed multigraphs

Parallel edges are represented by distinct elements of the edge type. The incidence subdivision
turns such a multigraph into a simple bipartite graph and transfers Euler circuits back to an
edge-distinguishing representation.
-/

namespace SimpleGraph

/-- A loopless multigraph whose parallel edges are distinguished by an edge type. -/
structure EdgeIndexedMultigraph (V : Type*) (E : Type*) where
  /-- The unordered endpoints of an edge. -/
  ends : E → Sym2 V
  /-- No edge has two equal endpoints. -/
  loopless : ∀ e v, ends e ≠ s(v, v)

namespace EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)

/-- A walk that records the identity of every traversed multiedge. -/
inductive IndexedWalk : V → V → Type _
  | nil (v : V) : IndexedWalk v v
  | cons {u v w : V} (e : E) (he : M.ends e = s(u, v))
      (p : IndexedWalk v w) : IndexedWalk u w

namespace IndexedWalk

/-- The vertices of an indexed walk, including both endpoints. -/
def support {u v : V} : M.IndexedWalk u v → List V
  | .nil w => [w]
  | .cons _ _ p => u :: p.support

/-- The edge identities traversed by an indexed walk. -/
def edges {u v : V} : M.IndexedWalk u v → List E
  | .nil _ => []
  | .cons e _ p => e :: p.edges

/-- An indexed walk is a trail when it uses no edge identity twice. -/
def IsTrail {u v : V} (p : M.IndexedWalk u v) : Prop :=
  p.edges.Nodup

/-- An indexed trail is Eulerian when it uses every edge identity. -/
def IsEulerian {u v : V} (p : M.IndexedWalk u v) : Prop :=
  p.IsTrail ∧ ∀ e, e ∈ p.edges

/-- Prepending an indexed edge prepends its identity to the edge list. -/
@[simp]
theorem edges_cons {u v w : V} (e : E) (he : M.ends e = s(u, v))
    (p : M.IndexedWalk v w) : (IndexedWalk.cons e he p).edges = e :: p.edges :=
  rfl

end IndexedWalk

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

private def disjointSumIncidenceEquiv {F : Type*} (N : EdgeIndexedMultigraph V F)
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
private def incidenceGraph : SimpleGraph (V ⊕ E) where
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

private instance [DecidableEq V] : DecidableRel M.incidenceGraph.Adj := by
  intro a b
  cases a <;> cases b <;> simp only [incidenceGraph, Inc] <;> infer_instance

/-- Keep the edge-index vertices from a list in the incidence subdivision. -/
private def edgeProjection : List (V ⊕ E) → List E
  | [] => []
  | Sum.inl _ :: l => edgeProjection l
  | Sum.inr e :: l => e :: edgeProjection l

/-- An incidence trail collapsed to an indexed walk, with its edge-list identity. -/
private structure IncidenceCollapse [DecidableEq V] {u v : V}
    (p : M.incidenceGraph.Walk (Sum.inl u) (Sum.inl v)) where
  walk : M.IndexedWalk u v
  edges_eq : walk.edges = edgeProjection p.support

/-- Collapse an incidence trail while retaining the edge-list identity. -/
private def collapseIncidence [DecidableEq V] {u v : V}
    (p : M.incidenceGraph.Walk (Sum.inl u) (Sum.inl v)) (hp : p.IsTrail) :
    M.IncidenceCollapse p := by
  cases hp₀ : p with
  | nil => exact ⟨.nil u, rfl⟩
  | @cons _ z _ h p =>
      cases z with
      | inl w => exact False.elim (M.not_incidenceGraph_adj_inl_inl u w h)
      | inr e =>
          cases hp₁ : p with
          | @cons _ z _ h' p' =>
              cases z with
              | inr f => exact False.elim (M.not_incidenceGraph_adj_inr_inr e f h')
              | inl w =>
                  rw [hp₀, hp₁] at hp
                  have huw : u ≠ w := by
                    intro huw
                    subst w
                    have hnot := (SimpleGraph.Walk.isTrail_cons h _).mp hp |>.2
                    apply hnot
                    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
                    left
                    exact Sym2.eq_swap
                  have he : M.ends e = s(u, w) :=
                    (Sym2.mem_and_mem_iff huw).mp ⟨h, h'⟩
                  have hdecr : p'.length < p.length := by
                    rw [hp₁, SimpleGraph.Walk.length_cons]
                    omega
                  let tail := collapseIncidence p' hp.of_cons.of_cons
                  refine ⟨IndexedWalk.cons e he tail.walk, ?_⟩
                  simp only [SimpleGraph.Walk.support_cons, edgeProjection]
                  exact congrArg (e :: ·) tail.edges_eq
termination_by p.length
decreasing_by
  apply lt_trans hdecr
  rw [hp₀, SimpleGraph.Walk.length_cons]
  omega

/-- Collapse an incidence-graph trail between original vertices to an edge-indexed walk. -/
private def indexedWalkOfIncidence [DecidableEq V] {u v : V}
    (p : M.incidenceGraph.Walk (Sum.inl u) (Sum.inl v)) (hp : p.IsTrail) :
    M.IndexedWalk u v :=
  (M.collapseIncidence p hp).walk
end EdgeIndexedMultigraph
end SimpleGraph
