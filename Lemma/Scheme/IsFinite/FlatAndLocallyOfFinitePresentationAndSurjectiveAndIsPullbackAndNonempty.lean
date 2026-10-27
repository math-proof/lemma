import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback.lean)
-/
@[path]
private lemma main
  {X R Y X' R' Y' : (Scheme : Type (u + 1))} {s t : R ⟶ X} {p : X ⟶ Y} [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  (hR : IsPullback s t p p) {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {gX : X' ⟶ X} (hX : IsPullback gX p' p g)
  {s' t' : R' ⟶ X'} {gR : R' ⟶ R} (hsq : IsPullback gR s' s gX) (htq : gR ≫ t = t' ≫ gX) (w' : s' ≫ p' = t' ≫ p') :
  -- imply
  IsFinite p' ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' ∧ IsPullback s' t' p' p' ∧ Nonempty (IsColimit (Cofork.ofπ p' w')) := by
  -- proof
  let _ : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hX inferInstance
  let _ : Flat p' := MorphismProperty.of_isPullback (P := @Flat) hX inferInstance
  let _ : LocallyOfFinitePresentation p' := MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hX inferInstance
  let _ : Surjective p' := MorphismProperty.of_isPullback (P := @Surjective) hX inferInstance
  have hker : IsPullback s' t' p' p' := by
    refine IsPullback.of_isLimit' ⟨w'⟩ (PullbackCone.IsLimit.mk _ (fun c => ?_) (fun c => ?_) (fun c => ?_) (fun c m hm₁ hm₂ => ?_))
    ·
      refine hsq.lift (hR.lift (c.fst ≫ gX) (c.snd ≫ gX) ?_) c.fst ?_
      · rw [Category.assoc, Category.assoc, hX.w, ← Category.assoc, ← Category.assoc, c.condition]
      · rw [IsPullback.lift_fst]
    · apply hsq.lift_snd _ _ _
    ·
      apply hX.hom_ext
      · rw [Category.assoc, ← htq, ← Category.assoc, hsq.lift_fst, hR.lift_snd]
      · rw [Category.assoc, ← w', ← Category.assoc, hsq.lift_snd, c.condition]
    ·
      apply hsq.hom_ext
      ·
        rw [hsq.lift_fst]
        apply hR.hom_ext
        · rw [IsPullback.lift_fst, Category.assoc, hsq.w, ← Category.assoc, hm₁]
        · rw [IsPullback.lift_snd, Category.assoc, htq, ← Category.assoc, hm₂]
      ·
        rw [hsq.lift_snd]
        apply hm₁
  have hk : IsKernelPair p' s' t' := hker
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, hker, ⟨?_⟩⟩
  apply hk.toCoequalizer (regularEpiOfEffectiveEpi p')


-- created on 2026-10-20
