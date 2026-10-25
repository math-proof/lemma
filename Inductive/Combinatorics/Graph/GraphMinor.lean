/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/GraphMinor.lean -/

/-
# Finite graphs and the graph-minor relation
-/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Structure.Combinatorics.Graph.GraphMinor


namespace MetaMathlibExt

/-- Single-step minor operation: `iso` is relabelling up to graph isomorphism;
`deleteVertex` is deletion of exactly one vertex (induced subgraph missing the
image of one vertex); `deleteEdge` is deletion of exactly one edge (vertices
identified up to an equivalence, edge sets agree except for one distinguished
edge); `contractEdge` collapses exactly one adjacent pair (a surjective map
identifying a single adjacent pair `a, b` and injective otherwise, with
adjacency in `H` given by images of adjacent pairs in `G` at distinct vertices,
so no loop is forced at the identified vertex).
Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem. -/
inductive MinorStep : FinGraph → FinGraph → Prop where
  | iso (H G : FinGraph) (e : H.G ≃g G.G) : MinorStep H G
  | deleteVertex (H G : FinGraph) (f : H.V ↪ G.V)
      (h_induced : ∀ u v, H.G.Adj u v ↔ G.G.Adj (f u) (f v))
      (a : G.V) (h_missing : ∀ x, (∃ y, f y = x) ↔ x ≠ a) : MinorStep H G
  | deleteEdge (H G : FinGraph) (e : H.V ≃ G.V)
      (h_sub : ∀ u v, H.G.Adj u v → G.G.Adj (e u) (e v))
      (x y : G.V) (h_edge : G.G.Adj x y)
      (h_miss : ¬H.G.Adj (e.symm x) (e.symm y))
      (h_only : ∀ u v, G.G.Adj (e u) (e v) →
        H.G.Adj u v ∨ (e u = x ∧ e v = y) ∨ (e u = y ∧ e v = x)) :
      MinorStep H G
  | contractEdge (H G : FinGraph) (f : G.V → H.V)
      (hsurj : Function.Surjective f)
      (a b : G.V) (h_adj : G.G.Adj a b) (h_ne : a ≠ b)
      (h_collapse : f a = f b)
      (h_single : ∀ x y, f x = f y →
        x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a))
      (h_adj_iff : ∀ u v, H.G.Adj u v ↔
        u ≠ v ∧ ∃ u' v', f u' = u ∧ f v' = v ∧ G.G.Adj u' v') :
      MinorStep H G

end MetaMathlibExt
