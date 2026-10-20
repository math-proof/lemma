import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.HNNEmbedding
open SemidirectProduct
open MathlibExt.GroupTheory.HNNEmbeddingWanted


/--
[higman_neumann_neumann_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma higman_neumann_neumann_embedding_eq
  {G : Type u} [Group G] [Countable G] :
-- imply
  ∃ (H : Type u) (hH : Group H) (a b : H), letI := by
-- proof
  apply MathlibExt.GroupTheory.HNNEmbeddingWanted.higman_neumann_neumann_embedding


-- created on 2026-10-20
