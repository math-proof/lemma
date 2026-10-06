import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_isIso_of_isIso_of_isPullback_of_flat_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_of_flat_of_surjective.lean)
-/
@[main]
private lemma main
  {S S' A B A' B' : Scheme.{0}}
  {b : S' ⟶ S} [Flat b] [Surjective b] [QuasiCompact b]
  {pA : A ⟶ S}
  {pB : B ⟶ S}
  {φ : A ⟶ B}
  {pA' : A' ⟶ S'}
  {pB' : B' ⟶ S'}
  {φ' : A' ⟶ B'}
  {gA : A' ⟶ A}
  {gB : B' ⟶ B}
  {sqA : IsPullback gA pA' pA b}
  {sqB : IsPullback gB pB' pB b}
-- given
  (hφ : φ ≫ pB = pA)
  (hφ' : φ' ≫ pB' = pA')
  (comm : φ' ≫ gB = gA ≫ φ)
  (hiso : IsIso φ') :
-- imply
  IsIso φ := by
-- proof
  have outer : IsPullback (φ' ≫ pB') gA b (φ ≫ pB) := by
    rw [hφ', hφ]
    exact sqA.flip
  have sq : IsPullback φ' gA gB φ := IsPullback.of_right outer comm sqB.flip

  have hS : Surjective gB := MorphismProperty.of_isPullback sqB.flip inferInstance
  have hF : Flat gB := MorphismProperty.of_isPullback sqB.flip inferInstance
  have hQ : QuasiCompact gB := MorphismProperty.of_isPullback sqB.flip inferInstance
  have hQ' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) gB := ⟨⟨hS, hF⟩, hQ⟩
  have hP : (MorphismProperty.isomorphisms Scheme.{0}) φ' := (MorphismProperty.isomorphisms.iff _).mpr hiso
  exact (MorphismProperty.isomorphisms.iff _).mp
    (MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq hQ' hP)


-- created on 2026-10-05
