import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Ideal.Support.IsRegularSequence
import Lemma.Fin.Image_CastSuccFinSetOfLtI.eq.ImageSetOfLtICastSucc

/--
Initial segment of a regular sequence remains regular
(atlas isRegularSequence_init).

[isRegularSequence_init](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  {A : Type*}
  [CommRing A]
  {k : ℕ}
  {f : Fin (k + 1) → A}
-- given
  (hreg : IsRegularSequence f) :
-- imply
  IsRegularSequence (f ∘ Fin.castSucc) := by
-- proof
  obtain ⟨hnzd, hnt⟩ := hreg
  constructor
  · intro j r hr
    suffices h : ∀ (I : Ideal A)
      (hI : I = Ideal.span (Set.image (f ∘ Fin.castSucc) {i : Fin k | (i : ℕ) < (j : ℕ)})),
      ∀ (r : A ⧸ I), r ≠ 0 → (Ideal.Quotient.mk I ((f ∘ Fin.castSucc) j)) • r ≠ 0 by
      exact h _ rfl r hr
    intro I hI r' hr'
    subst hI
    have hImgEq := Fin.Image_CastSuccFinSetOfLtI.eq.ImageSetOfLtICastSucc (f := f) (j := j)
    suffices h2 : ∀ (I : Ideal A)
      (hI : I = Ideal.span (Set.image f {i : Fin (k + 1) | (i : ℕ) < (Fin.castSucc j : ℕ)})),
      ∀ (r : A ⧸ I), r ≠ 0 → (Ideal.Quotient.mk I ((f ∘ Fin.castSucc) j)) • r ≠ 0 by
      exact h2 _ (by rw [← hImgEq]) r' hr'
    intro I' hI' r'' hr''
    subst hI'
    exact hnzd (Fin.castSucc j) r'' hr''
  · have hsub : Ideal.span (Set.range (f ∘ Fin.castSucc)) ≤ Ideal.span (Set.range f) := by
      apply Ideal.span_mono; intro x ⟨i, hi⟩; exact ⟨Fin.castSucc i, hi⟩
    rw [Ideal.Quotient.nontrivial_iff] at hnt ⊢
    exact ne_top_of_le_ne_top hnt hsub


-- created on 2026-10-24
