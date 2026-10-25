/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/MatrixTree.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Theorem.Combinatorics.SimpleGraph.MatrixTree


section

namespace MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

/-- Public equivalence between spanning subgraphs that are trees and trees below `G`
on the same vertex type. -/
def spanningTreeSubgraphEquiv {V : Type*} (G : SimpleGraph V) :
    {T : G.Subgraph // IsSpanningTree T} ≃ {H : SimpleGraph V // H ≤ G ∧ H.IsTree} := by
  classical
  refine
    { toFun := fun T => ⟨T.1.spanningCoe, T.1.spanningCoe_le, ?_⟩
      invFun := fun H => ⟨SimpleGraph.toSubgraph H.1 H.2.1,
        SimpleGraph.toSubgraph.isSpanning H.1 H.2.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact (SimpleGraph.Iso.isTree_iff (T.1.spanningCoeEquivCoeOfSpanning T.2.1)).mpr T.2.2
  · obtain ⟨H, hle, htreeH⟩ := H
    have hspan_eq : (SimpleGraph.toSubgraph H hle).spanningCoe = H := by
      apply SimpleGraph.ext
      funext v w
      rw [SimpleGraph.Subgraph.spanningCoe_adj, SimpleGraph.toSubgraph_adj]
    have h1 : (SimpleGraph.toSubgraph H hle).spanningCoe.IsTree := hspan_eq.symm ▸ htreeH
    exact (SimpleGraph.Iso.isTree_iff
      (SimpleGraph.Subgraph.spanningCoeEquivCoeOfSpanning _
        (SimpleGraph.toSubgraph.isSpanning H hle))).mp h1
  · intro T
    obtain ⟨T, hTspan, hTtree⟩ := T
    apply Subtype.ext
    change SimpleGraph.toSubgraph T.spanningCoe T.spanningCoe_le = T
    apply SimpleGraph.Subgraph.ext
    · have hv1 : (SimpleGraph.toSubgraph T.spanningCoe T.spanningCoe_le).verts = Set.univ :=
        SimpleGraph.Subgraph.isSpanning_iff.mp (SimpleGraph.toSubgraph.isSpanning _ _)
      have hv2 : T.verts = Set.univ := SimpleGraph.Subgraph.isSpanning_iff.mp hTspan
      rw [hv1, hv2]
    · funext v w
      rw [SimpleGraph.toSubgraph_adj, SimpleGraph.Subgraph.spanningCoe_adj]
  · intro H
    obtain ⟨H, hle, htreeH⟩ := H
    apply Subtype.ext
    change (SimpleGraph.toSubgraph H hle).spanningCoe = H
    apply SimpleGraph.ext
    funext v w
    rw [SimpleGraph.Subgraph.spanningCoe_adj, SimpleGraph.toSubgraph_adj]

end MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted
end
