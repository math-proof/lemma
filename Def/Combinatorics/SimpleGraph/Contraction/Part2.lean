/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.VertexConnectivity
import Theorem.Combinatorics.SimpleGraph.Contraction
/-!
# Contracting the complement of a vertex set

This file contracts every vertex outside a set to one new vertex. The construction is used by
the induction in Fleischner's theorem.
-/


namespace SimpleGraph

/-- Contract the complement of `D` to one vertex. -/
noncomputable def contractOutside {V : Type*} (G : SimpleGraph V) (D : Set V) :
    SimpleGraph (Option D) :=
  G.map (collapseOutside D)

end SimpleGraph
