import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_isClosedImmersion_pullbackLift_of_isClosedImmersion_pullbackLift_of_isPullback](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isClosedImmersion_pullbackLift_of_isClosedImmersion_pullbackLift_of_isPullback.lean)
-/
@[path]
private lemma main
  {G S : (Scheme : Type (u + 1))}
  (g : G ⟶ S)
  {R k L A : Type u} [CommRing R] [CommRing k] [CommRing L] [CommRing A] [Algebra R k] [Algebra R L]
  (sR : Spec (CommRingCat.of R) ⟶ S)
  (ι : Spec (CommRingCat.of L) ⟶ G)
  (h1 : ι ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ sR)
  (hcl : IsClosedImmersion (pullback.lift (f := g) (g := sR) ι (Spec.map (CommRingCat.ofHom (algebraMap R L))) h1))
  (s : Spec (CommRingCat.of k) ⟶ S)
  (hs : s = Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ sR)
  (a : RingHom L A)
  (c : RingHom k A)
  (hA : IsPullback (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom c)) (Spec.map (CommRingCat.ofHom (algebraMap R L))) (Spec.map (CommRingCat.ofHom (algebraMap R k))))
  (hsq : (Spec.map (CommRingCat.ofHom a) ≫ ι) ≫ g = Spec.map (CommRingCat.ofHom c) ≫ s) :
  IsClosedImmersion (pullback.lift (f := g) (g := s) (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq) := by
  subst hs
  let _ := hcl
  set j := pullback.lift (f := g) (g := sR) ι (Spec.map (CommRingCat.ofHom (algebraMap R L))) h1 with hj
  have hjfst : j ≫ pullback.fst g sR = ι := pullback.lift_fst _ _ _
  have hjsnd : j ≫ pullback.snd g sR = Spec.map (CommRingCat.ofHom (algebraMap R L)) := pullback.lift_snd _ _ _
  have hwcond : (Spec.map (CommRingCat.ofHom a) ≫ j) ≫ pullback.snd g sR = Spec.map (CommRingCat.ofHom c) ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) := by
    rw [Category.assoc, hjsnd]
    apply hA.w
  set w := pullback.lift (f := pullback.snd g sR) (g := Spec.map (CommRingCat.ofHom (algebraMap R k))) (Spec.map (CommRingCat.ofHom a) ≫ j) (Spec.map (CommRingCat.ofHom c)) hwcond with hw
  have hright : IsPullback (pullback.fst (pullback.snd g sR) (Spec.map (CommRingCat.ofHom (algebraMap R k)))) (pullback.snd (pullback.snd g sR) (Spec.map (CommRingCat.ofHom (algebraMap R k)))) (pullback.snd g sR) (Spec.map (CommRingCat.ofHom (algebraMap R k))) :=
    IsPullback.of_hasPullback _ _
  have houter : IsPullback (w ≫ pullback.snd (pullback.snd g sR) (Spec.map (CommRingCat.ofHom (algebraMap R k)))) (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom (algebraMap R k))) (j ≫ pullback.snd g sR) := by
    rw [hw, pullback.lift_snd, hjsnd]
    apply hA.flip
  have hleft : IsPullback w (Spec.map (CommRingCat.ofHom a)) (pullback.fst (pullback.snd g sR) (Spec.map (CommRingCat.ofHom (algebraMap R k)))) j := by
    refine IsPullback.of_right houter ?_ hright.flip
    rw [hw, pullback.lift_fst]
  let _ : IsClosedImmersion w :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hleft.flip inferInstance
  have heq : pullback.lift (f := g) (g := Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ sR) (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq = w ≫ (pullbackLeftPullbackSndIso g sR (Spec.map (CommRingCat.ofHom (algebraMap R k)))).hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullbackLeftPullbackSndIso_hom_fst, ← Category.assoc, hw, pullback.lift_fst, Category.assoc, hjfst]
    · rw [pullback.lift_snd, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, hw, pullback.lift_snd]
  rw [heq]
  infer_instance


-- created on 2026-10-20
