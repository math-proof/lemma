/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/PermutationStability.lean -/


import Def.GroupTheory.PermutationStability
import Lemma.Equiv.NormalizedHammingDistance.eq.Zero


namespace PermutationStabilityTest

open PermutationStability

/-- Normalization: reflexive distance vanishes. -/
example (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    normalizedHammingDistance n σ σ = 0 :=
  normalizedHammingDistance_self n σ

/-- Normalization: the distance lies in `[0, 1]`. -/
example (σ τ : Equiv.Perm (Fin 2)) :
    0 ≤ normalizedHammingDistance 2 σ τ ∧
      normalizedHammingDistance 2 σ τ ≤ 1 :=
  ⟨normalizedHammingDistance_nonneg 2 σ τ,
    normalizedHammingDistance_le_one (by norm_num) σ τ⟩

/-- The transposition on `Fin 2` disagrees with the identity everywhere. -/
example : normalizedHammingDistance 2 (Equiv.swap (0 : Fin 2) 1) 1 = 1 := by
  have h : hammingDist (fun i => Equiv.swap (0 : Fin 2) 1 i)
      (fun i => (1 : Equiv.Perm (Fin 2)) i) = 2 := by decide
  unfold normalizedHammingDistance
  rw [h]
  norm_num

/-- Equal-size flexible distance coincides with the normalized distance. -/
example (σ τ : Equiv.Perm (Fin 2)) :
    flexibleHammingDistance (le_refl 2) σ τ
      = normalizedHammingDistance 2 σ τ :=
  flexibleHammingDistance_diagonal (le_refl 2) σ τ

/-- The `m - n` penalty: an embedding-preserving large permutation sits at
exactly the unmatched-point fraction. -/
example (σ : Equiv.Perm (Fin 2)) (τ : Equiv.Perm (Fin 3))
    (h : 2 ≤ 3) (hτ : ∀ i, τ (Fin.castLE h i) = Fin.castLE h (σ i)) :
    flexibleHammingDistance h σ τ = 1 / 2 := by
  rw [flexibleHammingDistance_self h σ τ hτ]
  norm_num

end PermutationStabilityTest
