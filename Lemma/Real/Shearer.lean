import Mathlib
import sympy.Basic
import sympy.atlas.InformationTheory.Shearer
open Finset BigOperators Real
open MathlibExt.InformationTheory.Shearer


/--
[shearerMarginal_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerMarginal_nonneg_eq
  [Fintype α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ}
  {S : Finset (Fin n)}
  {y : ↥S → α}
-- given
  (hμ : ∀ x, 0 ≤ μ x) :
-- imply
  0 ≤ shearerMarginal μ S y := by
-- proof
  apply MathlibExt.InformationTheory.Shearer.shearerMarginal_nonneg μ hμ S y

/--
[shearerMarginal_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerMarginal_sum_eq
  [Fintype α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ}
  {S : Finset (Fin n)}
-- given
  (hμ_sum : ∑ x : (Fin n → α), μ x = 1) :
-- imply
  ∑ y : (↥S → α), shearerMarginal μ S y = 1 := by
-- proof
  apply MathlibExt.InformationTheory.Shearer.shearerMarginal_sum μ hμ_sum S

/--
[shearerMarginalEntropy_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerMarginalEntropy_mono_eq
  [Fintype α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ}
  {S T : Finset (Fin n)}
-- given
  (hμ : ∀ x, 0 ≤ μ x)
  (hTS : T ⊆ S) :
-- imply
  shearerMarginalEntropy μ T ≤ shearerMarginalEntropy μ S := by
-- proof
  apply MathlibExt.InformationTheory.Shearer.shearerMarginalEntropy_mono μ hμ S T hTS

/--
[shearerMarginalEntropy_submodular](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerMarginalEntropy_submodular_eq
  [Fintype α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ}
  {A B : Finset (Fin n)}
-- given
  (hμ : ∀ x, 0 ≤ μ x)
  (hμ_sum : ∑ x : (Fin n → α), μ x = 1) :
-- imply
  shearerMarginalEntropy μ (A ∪ B) + shearerMarginalEntropy μ (A ∩ B)
    ≤ shearerMarginalEntropy μ A + shearerMarginalEntropy μ B := by
-- proof
  apply MathlibExt.InformationTheory.Shearer.shearerMarginalEntropy_submodular μ hμ hμ_sum A B

/--
[shearerMarginalEntropy_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerMarginalEntropy_empty_eq
  [Fintype α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ}
-- given
  (hμ_sum : ∑ x : (Fin n → α), μ x = 1) :
-- imply
  shearerMarginalEntropy μ ∅ = 0 := by
-- proof
  apply MathlibExt.InformationTheory.Shearer.shearerMarginalEntropy_empty μ hμ_sum

/--
[shearerMarginalEntropy_univ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerMarginalEntropy_univ_eq
  [Fintype α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ} :
-- imply
  shearerMarginalEntropy μ Finset.univ = shearerFullEntropy μ := by
-- proof
  apply MathlibExt.InformationTheory.Shearer.shearerMarginalEntropy_univ μ

/--
[shearer_entropy_inequality_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearer_entropy_inequality_general_eq
  [Fintype α] [Nonempty α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ}
  {C : Finset (Finset (Fin n))}
  {k : ℕ}
-- given
  (hμ_nonneg : ∀ x, 0 ≤ μ x)
  (hμ_sum : ∑ x : (Fin n → α), μ x = 1)
  (hcover : ∀ i : Fin n, k ≤ (C.filter (fun S => i ∈ S)).card) :
-- imply
  (k : ℝ) * shearerFullEntropy μ ≤
    ∑ S ∈ C, shearerMarginalEntropy μ S := by
-- proof
  apply MathlibExt.InformationTheory.Shearer.shearer_entropy_inequality_general μ hμ_nonneg hμ_sum C k hcover

/--
[shearer_entropy_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearer_entropy_inequality_eq
  [Fintype α] [Nonempty α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ}
  {C : Finset (Finset (Fin n))}
  {k : ℕ}
-- given
  (hμ_nonneg : ∀ x, 0 ≤ μ x)
  (hμ_sum : ∑ x : (Fin n → α), μ x = 1)
  (hk : 0 < k)
  (hcover : ∀ i : Fin n, k ≤ (C.filter (fun S => i ∈ S)).card) :
-- imply
  (k : ℝ) * shearerFullEntropy μ ≤
    ∑ S ∈ C, shearerMarginalEntropy μ S := by
-- proof
  apply MathlibExt.InformationTheory.Shearer.shearer_entropy_inequality μ hμ_nonneg hμ_sum C k hk hcover


-- created on 2026-10-20
