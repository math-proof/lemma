/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.VertexConnectivity
import Def.Combinatorics.SimpleGraph.Contraction.Part2
/-!
# Contracting the complement of a vertex set

This file contracts every vertex outside a set to one new vertex. The construction is used by
the induction in Fleischner's theorem.
-/


namespace SimpleGraph

/-- Adjacency between surviving vertices is unchanged by contraction. -/
@[simp]
theorem contractOutside_adj_some {V : Type*} (G : SimpleGraph V) (D : Set V)
    (a b : D) :
    (G.contractOutside D).Adj (some a) (some b) ↔ G.Adj a b := by
  classical
  rw [contractOutside, map_adj']
  constructor
  · rintro ⟨_, u, v, huv, hu, hv⟩
    rw [collapseOutside_eq_some_iff] at hu hv
    simpa [hu, hv] using huv
  · intro hab
    refine ⟨?_, a, b, hab, ?_, ?_⟩
    · intro h
      exact G.ne_of_adj hab (congrArg Subtype.val (Option.some.inj h))
    · exact collapseOutside_of_mem D a.property
    · exact collapseOutside_of_mem D b.property

end SimpleGraph
