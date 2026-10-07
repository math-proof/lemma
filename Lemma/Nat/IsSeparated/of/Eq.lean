import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_isSeparated_of_isFinite_of_surjective_of_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isSeparated_of_isFinite_of_surjective_of_comp_eq.lean)
-/
@[main]
private lemma main
  {X Y S : Scheme.{0}}
  {p : X ⟶ Y} [IsFinite p] [Surjective p]
  {f : X ⟶ S} [IsSeparated f]
  {g : Y ⟶ S}
-- given
  (h : p ≫ g = f) :
-- imply
  IsSeparated g := by
-- proof
  let q : pullback f f ⟶ pullback g g := pullback.map f f g g p p (𝟙 S) (by simp [h]) (by simp [h])
  have : UniversallyClosed q :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) (inferInstance : UniversallyClosed p) (inferInstance : UniversallyClosed p)
      (by simp [h]) (by simp [h])

  have hsq : pullback.diagonal f ≫ q = p ≫ pullback.diagonal g := by
    apply pullback.hom_ext
    · erw [Category.assoc, Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.diagonal_fst, Category.id_comp,
        pullback.diagonal_fst, Category.comp_id]
    · erw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.diagonal_snd, Category.id_comp,
        pullback.diagonal_snd, Category.comp_id]

  have hcomp : ∀ {A B C : Scheme.{0}} (u : A ⟶ B) (v : B ⟶ C), (⇑(u ≫ v).base : A → C) = ⇑v.base ∘ ⇑u.base := by
    intro A B C u v; ext; simp
  have hrange : Set.range (pullback.diagonal g).base = q.base '' Set.range (pullback.diagonal f).base := by
    have h1 : Set.range (p ≫ pullback.diagonal g).base = Set.range (pullback.diagonal g).base := by
      rw [hcomp]; exact Function.Surjective.range_comp p.surjective _
    rw [← h1, ← hsq, hcomp, Set.range_comp]
  have hclosed : IsClosed (Set.range (pullback.diagonal g).base) := by
    rw [hrange]
    exact q.isClosedMap _ (pullback.diagonal f).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩


-- created on 2026-10-05
