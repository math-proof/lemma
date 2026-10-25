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
def parentExt {V : Type*} [DecidableEq V] (root : V)
    (f : { v : V // v ≠ root } → V) : V → V :=
  fun x => if h : x = root then root else f ⟨x, h⟩

/-- N0: rooted map: fixes the root and admits a rank function. -/
def IsRootedMap {V : Type*} (root : V) (g : V → V) : Prop :=
  g root = root ∧ ∃ h : V → ℕ, ∀ x, x ≠ root → h (g x) < h x

/-- N0: parent matrix with `1` on the diagonal minus the parent indicator. -/
def parentMatrix {V : Type*} [Fintype V] [DecidableEq V] (root : V)
    (f : { v : V // v ≠ root } → V) :
    Matrix { v : V // v ≠ root } { v : V // v ≠ root } ℤ :=
  Matrix.of fun v w => (if w = v then (1 : ℤ) else 0) - (if (w : V) = f v then 1 else 0)

end MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted
end
