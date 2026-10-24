import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.PermutationStability
open PermutationStability


namespace PermutationStability

/--
[normalizedHammingDistance_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/PermutationStability.lean)
-/
@[path]
lemma normalizedHammingDistance_self
  {n : ℕ}
  {σ : Equiv.Perm (Fin n)} :
-- imply
  normalizedHammingDistance n σ σ = 0 := by
-- proof
  simp [normalizedHammingDistance]

end PermutationStability

namespace PermutationStability

/--
[normalizedHammingDistance_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/PermutationStability.lean)
-/
@[path]
lemma normalizedHammingDistance_nonneg
  {n : ℕ}
  {σ τ : Equiv.Perm (Fin n)} :
-- imply
  0 ≤ normalizedHammingDistance n σ τ := by
-- proof
  unfold normalizedHammingDistance
  positivity

end PermutationStability

namespace PermutationStability

/--
[normalizedHammingDistance_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/PermutationStability.lean)
-/
@[path]
lemma normalizedHammingDistance_le_one
  {n : ℕ}
  {σ τ : Equiv.Perm (Fin n)}
-- given
  (hn : 0 < n) :
-- imply
  normalizedHammingDistance n σ τ ≤ 1 := by
-- proof
  unfold normalizedHammingDistance
  rw [div_le_one (Nat.cast_pos.mpr hn)]
  have h := hammingDist_le_card_fintype (x := fun i => σ i) (y := fun i => τ i)
  rw [Fintype.card_fin] at h
  exact Nat.cast_le.mpr h

end PermutationStability

namespace PermutationStability

/--
[flexibleHammingDistance_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/PermutationStability.lean)
-/
@[path]
lemma flexibleHammingDistance_self
  {n m : ℕ}
  {σ : Equiv.Perm (Fin n)}
  {τ : Equiv.Perm (Fin m)}
-- given
  (h : n ≤ m)
  (hτ : ∀ i, τ (Fin.castLE h i) = Fin.castLE h (σ i)) :
-- imply
  flexibleHammingDistance h σ τ = ((m - n : ℕ) : ℝ) / n := by
-- proof
  have hfun : (fun i => τ (Fin.castLE h i)) = (fun i => Fin.castLE h (σ i)) :=
    funext hτ
  unfold flexibleHammingDistance
  rw [hfun, hammingDist_self, Nat.zero_add]

end PermutationStability

namespace PermutationStability

/--
[flexibleHammingDistance_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/PermutationStability.lean)
-/
@[path]
lemma flexibleHammingDistance_diagonal
  {n : ℕ}
  {σ τ : Equiv.Perm (Fin n)}
-- given
  (h : n ≤ n) :
-- imply
  flexibleHammingDistance h σ τ = normalizedHammingDistance n σ τ := by
-- proof
  have hfun : (fun i => Fin.castLE h (σ i)) = (fun i => σ i) :=
    funext fun i => Fin.ext rfl
  have hfun' : (fun i => τ (Fin.castLE h i)) = (fun i => τ i) :=
    funext fun i => congrArg (τ ·) (Fin.ext rfl)
  unfold flexibleHammingDistance normalizedHammingDistance
  rw [hfun, hfun', Nat.sub_self, Nat.add_zero]

end PermutationStability


-- created on 2026-10-20
-- updated on 2026-10-23
