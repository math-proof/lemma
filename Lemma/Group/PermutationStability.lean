import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.PermutationStability
open PermutationStability


/--
[normalizedHammingDistance_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/PermutationStability.lean)
-/
@[path]
private lemma normalizedHammingDistance_self_eq
  {n : ℕ}
  {σ : Equiv.Perm (Fin n)} :
-- imply
  normalizedHammingDistance n σ σ = 0 := by
-- proof
  apply PermutationStability.normalizedHammingDistance_self n σ

/--
[normalizedHammingDistance_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/PermutationStability.lean)
-/
@[path]
private lemma normalizedHammingDistance_nonneg_eq
  {n : ℕ}
  {σ τ : Equiv.Perm (Fin n)} :
-- imply
  0 ≤ normalizedHammingDistance n σ τ := by
-- proof
  apply PermutationStability.normalizedHammingDistance_nonneg n σ τ

/--
[normalizedHammingDistance_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/PermutationStability.lean)
-/
@[path]
private lemma normalizedHammingDistance_le_one_eq
  {n : ℕ}
  {σ τ : Equiv.Perm (Fin n)}
-- given
  (hn : 0 < n) :
-- imply
  normalizedHammingDistance n σ τ ≤ 1 := by
-- proof
  apply PermutationStability.normalizedHammingDistance_le_one hn σ τ

/--
[flexibleHammingDistance_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/PermutationStability.lean)
-/
@[path]
private lemma flexibleHammingDistance_self_eq
  {n m : ℕ}
  {σ : Equiv.Perm (Fin n)}
  {τ : Equiv.Perm (Fin m)}
-- given
  (h : n ≤ m)
  (hτ : ∀ i, τ (Fin.castLE h i) = Fin.castLE h (σ i)) :
-- imply
  flexibleHammingDistance h σ τ = ((m - n : ℕ) : ℝ) / n := by
-- proof
  apply PermutationStability.flexibleHammingDistance_self h σ τ hτ

/--
[flexibleHammingDistance_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/PermutationStability.lean)
-/
@[path]
private lemma flexibleHammingDistance_diagonal_eq
  {n : ℕ}
  {σ τ : Equiv.Perm (Fin n)}
-- given
  (h : n ≤ n) :
-- imply
  flexibleHammingDistance h σ τ = normalizedHammingDistance n σ τ := by
-- proof
  apply PermutationStability.flexibleHammingDistance_diagonal h σ τ


-- created on 2026-10-20
