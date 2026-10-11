import Mathlib
import sympy.Basic
import sympy.matrices.inner_product_space.PolarSet

open InnerProductSpace.PolarSet.MetaMathlibExt

/--
[PolarSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/PolarSet.lean)
-/
@[path]
private lemma mem_polar_set_iff
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : Set E} {y : E} :
-- imply
  y ∈ polarSet A ↔ ∀ x ∈ A, inner ℝ x y ≤ 1 := by
-- proof
  apply mem_polarSet

/--
[PolarSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/PolarSet.lean)
-/
@[path]
private lemma polar_set_empty_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
-- imply
  polarSet (∅ : Set E) = Set.univ := by
-- proof
  apply polarSet_empty

/--
[PolarSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/PolarSet.lean)
-/
@[path]
private lemma zero_mem_polar_set_is
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (A : Set E) :
-- imply
  (0 : E) ∈ polarSet A := by
-- proof
  apply zero_mem_polarSet A

/--
[PolarSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/PolarSet.lean)
-/
@[path]
private lemma polar_set_subset_polar_set_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A B : Set E}
  (h : A ⊆ B) :
-- imply
  polarSet B ⊆ polarSet A := by
-- proof
  apply polarSet_subset_polarSet h

-- created on 2026-10-10
