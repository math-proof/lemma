import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.MatrixTree
open MathlibExt MathlibExt.Combinatorics MathlibExt.Combinatorics.SimpleGraph MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted


namespace MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

/--
[matrixTreeTest_entry_singleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/MatrixTree.lean)
-/
@[path]
lemma matrixTreeTest_entry_singleEdge
-- imply
  reducedLaplacian (⊤ : SimpleGraph (Fin 2)) 0 ⟨1, by decide⟩ ⟨1, by decide⟩ = 1 := by
-- proof
  decide

end MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

namespace MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

/--
[matrixTreeTest_entry_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/MatrixTree.lean)
-/
@[path]
lemma matrixTreeTest_entry_disconnected
-- imply
  reducedLaplacian (⊥ : SimpleGraph (Fin 2)) 0 ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 := by
-- proof
  decide

end MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

namespace MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

/--
[matrixTreeTest_entry_eq_lapMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/MatrixTree.lean)
-/
@[path]
lemma matrixTreeTest_entry_eq_lapMatrix
-- imply
  reducedLaplacian (⊤ : SimpleGraph (Fin 2)) 0 ⟨1, by decide⟩ ⟨1, by decide⟩ = (⊤ : SimpleGraph (Fin 2)).lapMatrix ℤ 1 1 := by
-- proof
  rw [reducedLaplacian_eq_lapMatrix_submatrix, Matrix.submatrix_apply]

end MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

namespace MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

/--
[matrixTreeTest_det_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/MatrixTree.lean)
-/
@[path]
lemma matrixTreeTest_det_singleton
-- imply
  (reducedLaplacian (⊥ : SimpleGraph (Fin 1)) 0).det = 1 := by
-- proof
  decide

end MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

namespace MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

/--
[matrixTreeTest_det_singleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/MatrixTree.lean)
-/
@[path]
lemma matrixTreeTest_det_singleEdge
-- imply
  (reducedLaplacian (⊤ : SimpleGraph (Fin 2)) 0).det = 1 := by
-- proof
  decide

end MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

namespace MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

/--
[matrixTreeTest_det_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/MatrixTree.lean)
-/
@[path]
lemma matrixTreeTest_det_disconnected
-- imply
  (reducedLaplacian (⊥ : SimpleGraph (Fin 2)) 0).det = 0 := by
-- proof
  decide

end MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted


-- created on 2026-10-23
