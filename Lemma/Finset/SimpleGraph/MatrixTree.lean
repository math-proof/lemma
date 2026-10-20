import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.MatrixTree
open MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted


/--
[laplacianInt_eq_lapMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/MatrixTree.lean)
-/
@[path]
private lemma laplacianInt_eq_lapMatrix_eq
  [Fintype V] [DecidableEq V]
  {G : _root_.SimpleGraph V} [DecidableRel G.Adj] :
-- imply
  laplacianInt G = G.lapMatrix ℤ := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted.laplacianInt_eq_lapMatrix G

/--
[reducedLaplacian_eq_lapMatrix_submatrix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/MatrixTree.lean)
-/
@[path]
private lemma reducedLaplacian_eq_lapMatrix_submatrix_eq
  [Fintype V] [DecidableEq V]
  {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
  {root : V} :
-- imply
  reducedLaplacian G root =
    (G.lapMatrix ℤ).submatrix Subtype.val Subtype.val := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted.reducedLaplacian_eq_lapMatrix_submatrix G root

/--
[numSpanningTrees_eq_card_trees](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/MatrixTree.lean)
-/
@[path]
private lemma numSpanningTrees_eq_card_trees_eq
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj] :
-- imply
  numSpanningTrees G = Nat.card {H : SimpleGraph V // H ≤ G ∧ H.IsTree} := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted.numSpanningTrees_eq_card_trees G

/--
[kirchhoff_matrix_tree_of_root](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/MatrixTree.lean)
-/
@[path]
private lemma kirchhoff_matrix_tree_of_root_eq
  :
-- imply
  ∀ {V : Type*} (G : _root_.SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (root : V),
    (reducedLaplacian G root).det = (numSpanningTrees G : ℤ) := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted.kirchhoff_matrix_tree_of_root

/--
[kirchhoff_matrix_tree_lapMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/MatrixTree.lean)
-/
@[path]
private lemma kirchhoff_matrix_tree_lapMatrix_eq
  :
-- imply
  ∀ {V : Type*} (G : _root_.SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (root : V),
    ((G.lapMatrix ℤ).submatrix (Subtype.val : { v : V // v ≠ root } → V)
    (Subtype.val : { v : V // v ≠ root } → V)).det
    = (numSpanningTrees G : ℤ) := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted.kirchhoff_matrix_tree_lapMatrix

/--
[kirchhoff_matrix_tree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/MatrixTree.lean)
-/
@[path]
private lemma kirchhoff_matrix_tree_eq
  :
-- imply
  ∀ {V : Type*} (G : _root_.SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Nonempty V] (root : V),
    (reducedLaplacian G root).det = (numSpanningTrees G : ℤ) := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted.kirchhoff_matrix_tree


-- created on 2026-10-20
