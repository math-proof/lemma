import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd.lean)
-/
@[path]
private lemma main
  {S S' Z X : (Scheme : Type (u + 1))}
  (z : Z ⟶ S)
  (f : X ⟶ S)
  (ι : S' ⟶ S) :
  IsIso (pullback.lift (pullback.lift (pullback.fst (pullback.fst z f ≫ z) ι ≫ pullback.fst z f) (pullback.snd (pullback.fst z f ≫ z) ι) (by simpa [Category.assoc] using pullback.condition)) (pullback.lift (pullback.fst (pullback.fst z f ≫ z) ι ≫ pullback.snd z f) (pullback.snd (pullback.fst z f ≫ z) ι) (by simpa [Category.assoc, ← pullback.condition (f := z) (g := f)] using pullback.condition)) (by rw [pullback.lift_snd, pullback.lift_snd]) : pullback (pullback.fst z f ≫ z) ι ⟶ pullback (pullback.snd z ι) (pullback.snd f ι)) := by
  have wA : (pullback.fst (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.fst z ι) ≫ z = (pullback.snd (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.fst f ι) ≫ f := by
    have h1 : pullback.fst z ι ≫ z = pullback.snd z ι ≫ ι := pullback.condition
    have h2 : pullback.fst f ι ≫ f = pullback.snd f ι ≫ ι := pullback.condition
    have h3 : pullback.fst (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.snd z ι = pullback.snd (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.snd f ι := pullback.condition
    simp only [Category.assoc, h1, h2]
    rw [← Category.assoc, h3, Category.assoc]
  let A : pullback (pullback.snd z ι) (pullback.snd f ι) ⟶ pullback z f :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst z ι) (pullback.snd _ _ ≫ pullback.fst f ι) wA
  have hA1 : A ≫ pullback.fst z f = pullback.fst _ _ ≫ pullback.fst z ι := pullback.lift_fst _ _ _
  have hA2 : A ≫ pullback.snd z f = pullback.snd _ _ ≫ pullback.fst f ι := pullback.lift_snd _ _ _
  have wAB : A ≫ (pullback.fst z f ≫ z) = (pullback.fst (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.snd z ι) ≫ ι := by
    rw [← Category.assoc, hA1, Category.assoc, Category.assoc]
    apply congrArg (pullback.fst (pullback.snd z ι) (pullback.snd f ι) ≫ ·) pullback.condition
  let inv : pullback (pullback.snd z ι) (pullback.snd f ι) ⟶ pullback (pullback.fst z f ≫ z) ι :=
    pullback.lift A (pullback.fst _ _ ≫ pullback.snd z ι) wAB
  have hI1 : inv ≫ pullback.fst (pullback.fst z f ≫ z) ι = A := pullback.lift_fst _ _ _
  have hI2 : inv ≫ pullback.snd (pullback.fst z f ≫ z) ι = pullback.fst _ _ ≫ pullback.snd z ι := pullback.lift_snd _ _ _
  refine ⟨⟨inv, ?_, ?_⟩⟩
  ·
    apply pullback.hom_ext
    ·
      apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, hI1, hA1, pullback.lift_fst_assoc, pullback.lift_fst]
      · simp only [Category.assoc, Category.id_comp, hI1, hA2, pullback.lift_snd_assoc, pullback.lift_fst]
    · simp only [Category.assoc, Category.id_comp, hI2, pullback.lift_fst_assoc, pullback.lift_snd]
  ·
    apply pullback.hom_ext
    ·
      apply pullback.hom_ext
      ·
        have hstep : inv ≫ (pullback.fst (pullback.fst z f ≫ z) ι ≫ pullback.fst z f) = pullback.fst (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.fst z ι := by
          rw [← Category.assoc, hI1, hA1]
        simp only [Category.assoc, Category.id_comp, pullback.lift_fst, hstep]
      · simp only [Category.assoc, Category.id_comp, pullback.lift_fst_assoc, pullback.lift_snd, hI2]
    ·
      apply pullback.hom_ext
      ·
        have hstep : inv ≫ (pullback.fst (pullback.fst z f ≫ z) ι ≫ pullback.snd z f) = pullback.snd (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.fst f ι := by
          rw [← Category.assoc, hI1, hA2]
        simp only [Category.assoc, Category.id_comp, pullback.lift_snd_assoc, pullback.lift_fst, hstep]
      ·
        simp only [Category.assoc, Category.id_comp, pullback.lift_snd, hI2]
        apply pullback.condition


-- created on 2026-10-20
