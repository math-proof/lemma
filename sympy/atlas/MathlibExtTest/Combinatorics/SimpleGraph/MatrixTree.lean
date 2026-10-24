/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/MatrixTree.lean -/


import sympy.atlas.Combinatorics.SimpleGraph.MatrixTree
import Lemma.Finset.SimpleGraph.MatrixTree


/-!
# Tests for the matrix-tree theorem public API

Exercises the reduced-Laplacian entries and the determinant/count agreement on
boundary cases (singleton, single edge, disconnected graph), using only public
declarations.
-/

namespace MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

/-- The promoted theorem applies to a single edge without unfolding proofs. -/
example : (reducedLaplacian (⊤ : SimpleGraph (Fin 2)) 0).det
    = (numSpanningTrees (⊤ : SimpleGraph (Fin 2)) : ℤ) :=
  kirchhoff_matrix_tree _ _

/-- The `Nonempty`-free theorem applies to a disconnected graph. -/
example : (reducedLaplacian (⊥ : SimpleGraph (Fin 2)) 0).det
    = (numSpanningTrees (⊥ : SimpleGraph (Fin 2)) : ℤ) :=
  kirchhoff_matrix_tree_of_root _ _

/-- The `lapMatrix`-stated theorem applies to a single edge. -/
example : (((⊤ : SimpleGraph (Fin 2)).lapMatrix ℤ).submatrix
    (Subtype.val : { v : Fin 2 // v ≠ 0 } → Fin 2)
    (Subtype.val : { v : Fin 2 // v ≠ 0 } → Fin 2)).det
    = (numSpanningTrees (⊤ : SimpleGraph (Fin 2)) : ℤ) :=
  kirchhoff_matrix_tree_lapMatrix _ _

/-- The Laplacian bridge applies to a single edge. -/
example : laplacianInt (⊤ : SimpleGraph (Fin 2)) = (⊤ : SimpleGraph (Fin 2)).lapMatrix ℤ :=
  laplacianInt_eq_lapMatrix _

/-- The reduced-Laplacian bridge applies to a single edge. -/
example : reducedLaplacian (⊤ : SimpleGraph (Fin 2)) 0 =
    ((⊤ : SimpleGraph (Fin 2)).lapMatrix ℤ).submatrix Subtype.val Subtype.val :=
  reducedLaplacian_eq_lapMatrix_submatrix _ _

/-- The count characterization applies to a single edge. -/
example : numSpanningTrees (⊤ : SimpleGraph (Fin 2))
    = Nat.card {H : SimpleGraph (Fin 2) // H ≤ ⊤ ∧ H.IsTree} :=
  numSpanningTrees_eq_card_trees _

end MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted
