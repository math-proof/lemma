/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.VertexConnectivity
import Theorem.Combinatorics.SimpleGraph.Contraction.Part2
/-!
# Contracting the complement of a vertex set

This file contracts every vertex outside a set to one new vertex. The construction is used by
the induction in Fleischner's theorem.
-/


namespace SimpleGraph

noncomputable def induceContractOutsideSomeHom {V : Type*}
    (G : SimpleGraph V) (D : Set V) :
    G.induce D →g
      (G.contractOutside D).induce
        (↑({none} : Finset (Option D)) : Set (Option D))ᶜ where
  toFun a := ⟨some a, by simp⟩
  map_rel' := by
    intro a b hab
    exact contractOutside_adj_some G D a b |>.mpr (induce_adj.mp hab)

end SimpleGraph
