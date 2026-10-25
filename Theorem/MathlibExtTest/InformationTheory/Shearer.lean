/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/InformationTheory/Shearer.lean -/


import Def.InformationTheory.Shearer
import Lemma.Real.Shearer
/-!
# Shearer's entropy inequality API checks

Entropy of a point mass, the empty and full marginals, monotonicity, submodularity, and
two-coordinate subadditivity as a case of the inequality.
-/


namespace MathlibExtTest.InformationTheory.Shearer

open MathlibExt.InformationTheory.Shearer

-- A point mass on `Fin 0 → Bool` has zero entropy.
example : shearerFullEntropy (fun _ : Fin 0 → Bool => (1 : ℝ)) = 0 := by
  simp [shearerFullEntropy]

example {n : ℕ} (μ : (Fin n → Bool) → ℝ) (hμ : ∑ x, μ x = 1) :
    shearerMarginalEntropy μ ∅ = 0 ∧ shearerMarginalEntropy μ Finset.univ = shearerFullEntropy μ :=
  ⟨shearerMarginalEntropy_empty μ hμ, shearerMarginalEntropy_univ μ⟩

example {n : ℕ} (μ : (Fin n → Bool) → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (S : Finset (Fin n)) :
    0 ≤ shearerMarginalEntropy μ S ∧ shearerMarginalEntropy μ S ≤ shearerFullEntropy μ := by
  rw [← shearerMarginalEntropy_univ μ, ← shearerMarginalEntropy_empty μ hμ1]
  exact ⟨shearerMarginalEntropy_mono μ hμ _ _ (Finset.empty_subset S),
    shearerMarginalEntropy_mono μ hμ _ _ (Finset.subset_univ S)⟩

-- Subadditivity for two coordinates, from the cover `{{0}, {1}}` with `k = 1`.
example (μ : (Fin 2 → Bool) → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) :
    shearerFullEntropy μ ≤ shearerMarginalEntropy μ {0} + shearerMarginalEntropy μ {1} := by
  have h := shearer_entropy_inequality_general μ hμ hμ1 {{0}, {1}} 1 (by decide)
  simpa using h

-- Submodularity with disjoint sets is subadditivity.
example (μ : (Fin 2 → Bool) → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) :
    shearerMarginalEntropy μ ({0} ∪ {1}) + shearerMarginalEntropy μ ∅ ≤
      shearerMarginalEntropy μ {0} + shearerMarginalEntropy μ {1} := by
  simpa using shearerMarginalEntropy_submodular μ hμ hμ1 {0} {1}

end MathlibExtTest.InformationTheory.Shearer
