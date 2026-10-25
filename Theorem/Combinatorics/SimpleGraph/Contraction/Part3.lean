/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.VertexConnectivity
import Def.Combinatorics.SimpleGraph.Contraction.Part3
/-!
# Contracting the complement of a vertex set

This file contracts every vertex outside a set to one new vertex. The construction is used by
the induction in Fleischner's theorem.
-/


namespace SimpleGraph

/-- Contracting the complement of a connected set with at least two vertices in a
2-vertex-connected graph produces another 2-vertex-connected graph. -/
theorem IsVertexConnected.contractOutside {V : Type*} [Fintype V]
    {G : SimpleGraph V} {D : Set V} [Fintype D] (hG : G.IsVertexConnected 2)
    (hDcard : 1 < Fintype.card D) (hDconn : (G.induce D).Connected)
    (hDout : Dᶜ.Nonempty) : (G.contractOutside D).IsVertexConnected 2 := by
  classical
  rw [isVertexConnected_two_iff]
  refine ⟨?_, hG.connected (by omega) |>.contractOutside hDout, ?_⟩
  · simp only [Fintype.card_option]
    omega
  · intro z
    cases z with
    | none => exact hDconn.contractOutside_delete_none
    | some d => exact hG.contractOutside_delete_some hDout d

end SimpleGraph
