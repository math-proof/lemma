import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.PerronFrobeniusProof
open Finset BigOperators Matrix PerronFrobenius


/--
[continuous_mulVec_component](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PerronFrobeniusProof.lean)
-/
@[path]
private lemma continuous_mulVec_component_eq
  [DecidableEq ι]
  [Fintype ι]
  [Nonempty ι]
  {M : Matrix ι ι ℝ}
  {i : ι} :
-- imply
  Continuous (fun p : (ι → ℝ) × ℝ => M.mulVec p.1 i) := by
-- proof
  apply PerronFrobenius.continuous_mulVec_component M i

/--
[simplex_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PerronFrobeniusProof.lean)
-/
@[path]
private lemma simplex_le_one_eq
  [DecidableEq ι]
  [Fintype ι]
  [Nonempty ι]
  {v : ι → ℝ}
  {i : ι}
-- given
  (hv : v ∈ stdSimplex ℝ ι) :
-- imply
  v i ≤ 1 := by
-- proof
  apply PerronFrobenius.simplex_le_one hv i

/--
[mulVec_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PerronFrobeniusProof.lean)
-/
@[path]
private lemma mulVec_pos_eq
  [DecidableEq ι]
  [Fintype ι]
  [Nonempty ι]
  {M : Matrix ι ι ℝ}
  {v : ι → ℝ}
  {i : ι}
-- given
  (hM : ∀ i j, 0 < M i j)
  (hv : v ∈ stdSimplex ℝ ι) :
-- imply
  0 < M.mulVec v i := by
-- proof
  apply PerronFrobenius.mulVec_pos M hM hv i

/--
[cwSet_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PerronFrobeniusProof.lean)
-/
@[path]
private lemma cwSet_closed_eq
  [DecidableEq ι]
  [Fintype ι]
  [Nonempty ι]
  {M : Matrix ι ι ℝ} :
-- imply
  IsClosed (CWSet M) := by
-- proof
  apply PerronFrobenius.cwSet_closed M

/--
[cwSet_subset_compact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PerronFrobeniusProof.lean)
-/
@[path]
private lemma cwSet_subset_compact_eq
  [DecidableEq ι]
  [Fintype ι]
  [Nonempty ι]
  {M : Matrix ι ι ℝ}
-- given
  (hM : ∀ i j, 0 < M i j) :
-- imply
  CWSet M ⊆ (stdSimplex ℝ ι) ×ˢ (Set.Icc 0 (∑ i : ι, ∑ j : ι, M i j)) := by
-- proof
  apply PerronFrobenius.cwSet_subset_compact M hM

/--
[cwSet_compact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PerronFrobeniusProof.lean)
-/
@[path]
private lemma cwSet_compact_eq
  [DecidableEq ι]
  [Fintype ι]
  [Nonempty ι]
  {M : Matrix ι ι ℝ}
-- given
  (hM : ∀ i j, 0 < M i j) :
-- imply
  IsCompact (CWSet M) := by
-- proof
  apply PerronFrobenius.cwSet_compact M hM

/--
[cwSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PerronFrobeniusProof.lean)
-/
@[path]
private lemma cwSet_nonempty_eq
  [DecidableEq ι]
  [Fintype ι]
  [Nonempty ι]
  {M : Matrix ι ι ℝ}
-- given
  (hM : ∀ i j, 0 < M i j) :
-- imply
  (CWSet M).Nonempty := by
-- proof
  apply PerronFrobenius.cwSet_nonempty M hM


-- created on 2026-10-23
