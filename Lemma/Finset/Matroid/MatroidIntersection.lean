import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Matroid.MatroidIntersection
open MathlibExt.Combinatorics.Matroid.MatroidIntersectionWanted


/--
[exists_common_indep_of_cut_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/MatroidIntersection.lean)
-/
@[path]
private lemma exists_common_indep_of_cut_le_eq
  [DecidableEq α]
  {E : Finset α}
  {k : ℕ}
  {r₁ r₂ : Finset α → ℕ}
-- given
  (hle₁ : ∀ X, r₁ X ≤ X.card)
  (hle₂ : ∀ X, r₂ X ≤ X.card)
  (hmono₁ : ∀ X Y, X ⊆ Y → r₁ X ≤ r₁ Y)
  (hmono₂ : ∀ X Y, X ⊆ Y → r₂ X ≤ r₂ Y)
  (hsub₁ : ∀ X Y, r₁ (X ∩ Y) + r₁ (X ∪ Y) ≤ r₁ X + r₁ Y)
  (hsub₂ : ∀ X Y, r₂ (X ∩ Y) + r₂ (X ∪ Y) ≤ r₂ X + r₂ Y)
  (hcut : ∀ X, X ⊆ E → k ≤ r₁ X + r₂ (E \ X)) :
-- imply
  ∃ I, I ⊆ E ∧ r₁ I = I.card ∧ r₂ I = I.card ∧ k ≤ I.card := by
-- proof
  apply MathlibExt.Combinatorics.Matroid.MatroidIntersectionWanted.exists_common_indep_of_cut_le E k r₁ r₂ hle₁ hle₂ hmono₁ hmono₂ hsub₁ hsub₂ hcut

/--
[edmonds_matroid_intersection'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/MatroidIntersection.lean)
-/
@[path]
private lemma edmonds_matroid_intersection'_eq
  [Finite α]
  {M₁ M₂ : Matroid α}
  {k : ℕ} :
-- imply
  (∃ I : Finset α, M₁.Indep (I : Set α) ∧
    M₂.Indep (I : Set α) ∧ k ≤ I.card) ↔
    ∀ X : Set α, (k : ℕ∞) ≤ M₁.eRk X + M₂.eRk Xᶜ := by
-- proof
  apply MathlibExt.Combinatorics.Matroid.MatroidIntersectionWanted.edmonds_matroid_intersection'

/--
[edmonds_matroid_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/MatroidIntersection.lean)
-/
@[path]
private lemma edmonds_matroid_intersection_eq
  [Fintype α] [DecidableEq α]
  {M₁ M₂ : Matroid α}
  {k : ℕ}
-- given
  (h₁ : M₁.E = Set.univ)
  (h₂ : M₂.E = Set.univ) :
-- imply
  (∃ I : Finset α, M₁.Indep (I : Set α) ∧
    M₂.Indep (I : Set α) ∧ k ≤ I.card) ↔
    ∀ X : Set α, (k : ℕ∞) ≤ M₁.eRk X + M₂.eRk Xᶜ := by
-- proof
  apply MathlibExt.Combinatorics.Matroid.MatroidIntersectionWanted.edmonds_matroid_intersection h₁ h₂


-- created on 2026-10-20
