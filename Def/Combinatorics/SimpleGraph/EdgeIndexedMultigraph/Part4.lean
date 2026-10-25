/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Trails
import Lemma.SimpleGraph.EulerCircuit
import Structure.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part2
/-!
# Finite edge-indexed multigraphs

Parallel edges are represented by distinct elements of the edge type. The incidence subdivision
turns such a multigraph into a simple bipartite graph and transfers Euler circuits back to an
edge-distinguishing representation.
-/


namespace SimpleGraph

namespace EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)

/-- Collapse an incidence trail while retaining the edge-list identity. -/
def collapseIncidence [DecidableEq V] {u v : V}
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
def indexedWalkOfIncidence [DecidableEq V] {u v : V}
    (p : M.incidenceGraph.Walk (Sum.inl u) (Sum.inl v)) (hp : p.IsTrail) :
    M.IndexedWalk u v :=
  (M.collapseIncidence p hp).walk

end EdgeIndexedMultigraph
end SimpleGraph
