/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/MatrixTree.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

section
namespace MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

/-!
# Matrix-tree and Cayley landmarks

Records Kirchhoff's matrix-tree theorem and Cayley's formula.
-/

/-- Integer graph Laplacian: diagonal is degree, off-diagonal is `-1` on
edges. -/
def laplacianInt {V : Type*} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] : Matrix V V ℤ :=
  Matrix.of fun u v => if u = v then (G.degree u : ℤ) else if G.Adj u v then -1 else 0

/-- Reduced Laplacian after deleting a chosen root vertex. -/
def reducedLaplacian {V : Type*} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] (root : V) :
    Matrix { v : V // v ≠ root } { v : V // v ≠ root } ℤ :=
  Matrix.of fun ⟨u, _⟩ ⟨v, _⟩ => laplacianInt G u v

/-- Spanning-tree predicate requiring both spanning and tree. -/
def IsSpanningTree {V : Type*} {G : _root_.SimpleGraph V} (T : G.Subgraph) : Prop :=
  T.IsSpanning ∧ T.coe.IsTree

/-- Finite number of spanning trees using subgraph and `IsTree`. -/
noncomputable def numSpanningTrees {V : Type*} (G : _root_.SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] : ℕ :=
  Nat.card { T : G.Subgraph // IsSpanningTree T }

/-! ## Helpers for the matrix-tree proof (blueprint nodes N0–N13). -/

/-- N0: extend a parent map on non-root vertices to all vertices. -/
private def parentExt {V : Type*} [DecidableEq V] (root : V)
    (f : { v : V // v ≠ root } → V) : V → V :=
  fun x => if h : x = root then root else f ⟨x, h⟩

/-- N0: rooted map: fixes the root and admits a rank function. -/
private def IsRootedMap {V : Type*} (root : V) (g : V → V) : Prop :=
  g root = root ∧ ∃ h : V → ℕ, ∀ x, x ≠ root → h (g x) < h x

/-- N0: parent matrix with `1` on the diagonal minus the parent indicator. -/
private def parentMatrix {V : Type*} [Fintype V] [DecidableEq V] (root : V)
    (f : { v : V // v ≠ root } → V) :
    Matrix { v : V // v ≠ root } { v : V // v ≠ root } ℤ :=
  Matrix.of fun v w => (if w = v then (1 : ℤ) else 0) - (if (w : V) = f v then 1 else 0)

@[simp] private theorem parentExt_root {V : Type*} [DecidableEq V] (root : V)
    (f : { v : V // v ≠ root } → V) : parentExt root f root = root := by
  simp [parentExt]

@[simp] private theorem parentExt_apply {V : Type*} [DecidableEq V] (root : V)
    (f : { v : V // v ≠ root } → V) (v : { v : V // v ≠ root }) :
    parentExt root f (v : V) = f v := by
  simp [parentExt, v.2]

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
