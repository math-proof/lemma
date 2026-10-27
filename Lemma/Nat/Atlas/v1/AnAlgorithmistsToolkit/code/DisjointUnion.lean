import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.AnAlgorithmistsToolkit.code.DisjointUnion
open DisjointUnion
open Matrix SimpleGraph Finset
open Polynomial


namespace DisjointUnion

/--
[neighborFinset_sum_inl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/DisjointUnion.lean)
-/
@[path]
lemma neighborFinset_sum_inl
  [Fintype V₁]
  [Fintype V₂]
  [DecidableEq V₁]
  [DecidableEq V₂]
  {G : SimpleGraph V₁}
  {H : SimpleGraph V₂}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {v : V₁} :
-- imply
  (G ⊕g H).neighborFinset (Sum.inl v) = (G.neighborFinset v).map ⟨Sum.inl, Sum.inl_injective⟩ := by
-- proof
  ext w
  simp only [SimpleGraph.neighborFinset, Set.mem_toFinset, SimpleGraph.neighborSet,
    Set.mem_setOf_eq, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro hadj
    cases w with
    | inl w => exact ⟨w, hadj, rfl⟩
    | inr w => exact absurd hadj (by simp [SimpleGraph.sum])
  · rintro ⟨w, hadj, rfl⟩
    exact hadj

end DisjointUnion

namespace DisjointUnion

/--
[neighborFinset_sum_inr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/DisjointUnion.lean)
-/
@[path]
lemma neighborFinset_sum_inr
  [Fintype V₁]
  [Fintype V₂]
  [DecidableEq V₁]
  [DecidableEq V₂]
  {G : SimpleGraph V₁}
  {H : SimpleGraph V₂}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {w : V₂} :
-- imply
  (G ⊕g H).neighborFinset (Sum.inr w) = (H.neighborFinset w).map ⟨Sum.inr, Sum.inr_injective⟩ := by
-- proof
  ext v
  simp only [SimpleGraph.neighborFinset, Set.mem_toFinset, SimpleGraph.neighborSet,
    Set.mem_setOf_eq, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro hadj
    cases v with
    | inl v => exact absurd hadj (by simp [SimpleGraph.sum])
    | inr v => exact ⟨v, hadj, rfl⟩
  · rintro ⟨v, hadj, rfl⟩
    exact hadj

end DisjointUnion

namespace DisjointUnion

/--
[degree_sum_inl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/DisjointUnion.lean)
-/
@[path]
lemma degree_sum_inl
  [Fintype V₁]
  [Fintype V₂]
  [DecidableEq V₁]
  [DecidableEq V₂]
  {G : SimpleGraph V₁}
  {H : SimpleGraph V₂}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {v : V₁} :
-- imply
  (G ⊕g H).degree (Sum.inl v) = G.degree v := by
-- proof
  simp only [SimpleGraph.degree, neighborFinset_sum_inl, Finset.card_map]

end DisjointUnion

namespace DisjointUnion

/--
[degree_sum_inr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/DisjointUnion.lean)
-/
@[path]
lemma degree_sum_inr
  [Fintype V₁]
  [Fintype V₂]
  [DecidableEq V₁]
  [DecidableEq V₂]
  {G : SimpleGraph V₁}
  {H : SimpleGraph V₂}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {w : V₂} :
-- imply
  (G ⊕g H).degree (Sum.inr w) = H.degree w := by
-- proof
  simp only [SimpleGraph.degree, neighborFinset_sum_inr, Finset.card_map]

end DisjointUnion

namespace DisjointUnion

/--
[lapMatrix_sum_eq_fromBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/DisjointUnion.lean)
-/
@[path]
lemma lapMatrix_sum_eq_fromBlocks
  [Fintype V₁]
  [Fintype V₂]
  [DecidableEq V₁]
  [DecidableEq V₂]
  {G : SimpleGraph V₁}
  {H : SimpleGraph V₂}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj] :
-- imply
  (G ⊕g H).lapMatrix ℝ = Matrix.fromBlocks (G.lapMatrix ℝ) 0 0 (H.lapMatrix ℝ) := by
-- proof
  ext (i | i) (j | j)
  ·
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      fromBlocks_apply₁₁, sub_apply, diagonal_apply, of_apply,
      SimpleGraph.sum, Sum.inl.injEq]
    congr 1
    split_ifs with h
    · congr 1; exact_mod_cast degree_sum_inl G H i
    · rfl
  ·
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      fromBlocks_apply₁₂, sub_apply, diagonal_apply, of_apply,
      SimpleGraph.sum, zero_apply]
    simp [Sum.inl_ne_inr]
  ·
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      fromBlocks_apply₂₁, sub_apply, diagonal_apply, of_apply,
      SimpleGraph.sum, zero_apply]
    simp [Sum.inr_ne_inl]
  ·
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      fromBlocks_apply₂₂, sub_apply, diagonal_apply, of_apply,
      SimpleGraph.sum, Sum.inr.injEq]
    congr 1
    split_ifs with h
    · congr 1; exact_mod_cast degree_sum_inr G H i
    · rfl
section DisjointUnionSpectrum
variable {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂] [DecidableEq V₁] [DecidableEq V₂]
variable (G : SimpleGraph V₁) (H : SimpleGraph V₂) [DecidableRel G.Adj] [DecidableRel H.Adj]
open Polynomial

end DisjointUnion

namespace DisjointUnion

/--
[charpoly_roots_fromBlocks_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/DisjointUnion.lean)
-/
@[path]
lemma charpoly_roots_fromBlocks_zero
  [Fintype V₁]
  [Fintype V₂]
  [DecidableEq V₁]
  [DecidableEq V₂]
  {G : SimpleGraph V₁}
  {H : SimpleGraph V₂}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  [CommRing R]
  [IsDomain R]
  [Fintype m]
  [Fintype n]
  [DecidableEq m]
  [DecidableEq n]
  {A : Matrix m m R}
  {B : Matrix n n R} :
-- imply
  (Matrix.fromBlocks A 0 0 B).charpoly.roots = A.charpoly.roots + B.charpoly.roots := by
-- proof
  rw [Matrix.charpoly_fromBlocks_zero₁₂]
  exact Polynomial.roots_mul (mul_ne_zero (Matrix.charpoly_monic A).ne_zero
    (Matrix.charpoly_monic B).ne_zero)

end DisjointUnion

namespace DisjointUnion

/--
[lapMatrix_sum_charpoly_roots](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/DisjointUnion.lean)
-/
@[path]
lemma lapMatrix_sum_charpoly_roots
  [Fintype V₁]
  [Fintype V₂]
  [DecidableEq V₁]
  [DecidableEq V₂]
  {G : SimpleGraph V₁}
  {H : SimpleGraph V₂}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj] :
-- imply
  ((G ⊕g H).lapMatrix ℝ).charpoly.roots = (G.lapMatrix ℝ).charpoly.roots + (H.lapMatrix ℝ).charpoly.roots := by
-- proof
  rw [lapMatrix_sum_eq_fromBlocks]
  exact charpoly_roots_fromBlocks_zero (G.lapMatrix ℝ) (H.lapMatrix ℝ)

end DisjointUnion


-- created on 2026-10-23
