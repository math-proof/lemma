import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_exists_isPullback_fst_toSpecAway_of_charts_of_isPullback](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_isPullback_fst_toSpecAway_of_charts_of_isPullback.lean)
-/
@[path]
private lemma main
  {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S)
  (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
  {Y : (Scheme : Type (u + 1))} (f : Y ⟶ Spec (CommRingCat.of S))
  {A' : Fin k → (Scheme : Type (u + 1))} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (ι : ∀ i, A' i ⟶ Y)
  [∀ i, IsOpenImmersion (ι i)]
  (hsq : ∀ i, CategoryTheory.IsPullback (ι i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
  (i j : Fin k) :
    ∃ (ρ₁ : AlgHom S (B i) (Localization.Away (r i * r j))) (fP : Limits.pullback (ι i) (ι j) ⟶ Spec (CommRingCat.of (Localization.Away (r i * r j)))), (let _ : Algebra (B i) (Localization.Away (r i * r j)) := ρ₁.toRingHom.toAlgebra; IsLocalization.Away (algebraMap S (B i) (r j)) (Localization.Away (r i * r j))) ∧ CategoryTheory.IsPullback (Limits.pullback.fst (ι i) (ι j)) fP (f' i) (Spec.map (CommRingCat.ofHom ρ₁.toRingHom)) ∧ fP ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i * r j)))) = Limits.pullback.fst (ι i) (ι j) ≫ ι i ≫ f := by
  classical
  let L₁ := Localization.Away (algebraMap S (B i) (r j))
  let L₂ := Localization.Away (algebraMap S (B j) (r i))
  let _ : IsLocalization.Away (r i * r j) L₁ := inferInstance
  let _ : IsLocalization.Away (r i * r j) L₂ := inferInstance
  let e₁ : AlgEquiv S L₁ (Localization.Away (r i * r j)) := IsLocalization.algEquiv (Submonoid.powers (r i * r j)) L₁ _
  let e₂ : AlgEquiv S L₂ (Localization.Away (r i * r j)) := IsLocalization.algEquiv (Submonoid.powers (r i * r j)) L₂ _
  let ρ₁ : AlgHom S (B i) (Localization.Away (r i * r j)) := e₁.toAlgHom.comp (IsScalarTower.toAlgHom S (B i) L₁)
  let ρ₂ : AlgHom S (B j) (Localization.Away (r i * r j)) := e₂.toAlgHom.comp (IsScalarTower.toAlgHom S (B j) L₂)
  let algI : Algebra (B i) (Localization.Away (r i * r j)) := ρ₁.toRingHom.toAlgebra
  let algJ : Algebra (B j) (Localization.Away (r i * r j)) := ρ₂.toRingHom.toAlgebra
  have hawayI : IsLocalization.Away (algebraMap S (B i) (r j)) (Localization.Away (r i * r j)) := by
    let h₁ : AlgEquiv (B i) L₁ (Localization.Away (r i * r j)) := AlgEquiv.ofRingEquiv (f := e₁.toRingEquiv) (fun x => rfl)
    apply IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap S (B i) (r j))) h₁
  have hawayJ : IsLocalization.Away (algebraMap S (B j) (r i)) (Localization.Away (r i * r j)) := by
    let h₂ : AlgEquiv (B j) L₂ (Localization.Away (r i * r j)) := AlgEquiv.ofRingEquiv (f := e₂.toRingEquiv) (fun x => rfl)
    apply IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap S (B j) (r i))) h₂
  have hpo : IsPushout (CommRingCat.ofHom (algebraMap S (B j))) (CommRingCat.ofHom (algebraMap S (B i)))
    (CommRingCat.ofHom (algebraMap (B j) (Localization.Away (r i * r j)))) (CommRingCat.ofHom ρ₁.toRingHom) := by
    let _ := hawayJ
    refine CommRingCat.isPushout_of_isLocalization (algebraMap S (B j)) ρ₁.toRingHom ?_ (Submonoid.powers (r i))
    apply RingHom.ext fun s => (ρ₁.commutes s).trans (ρ₂.commutes s).symm
  have hbot : IsPullback (Spec.map (CommRingCat.ofHom ρ₁.toRingHom)) (Spec.map (CommRingCat.ofHom ρ₂.toRingHom))
    (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))) (Spec.map (CommRingCat.ofHom (algebraMap S (B j)))) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip
  have hR1 : IsPullback (pullback.fst (ι i) (ι j)) (pullback.snd (ι i) (ι j) ≫ f' j) (ι i ≫ f)
    (Spec.map (CommRingCat.ofHom (algebraMap S (B j)))) :=
    (IsPullback.of_hasPullback (ι i) (ι j)).paste_vert (hsq j)
  have hw : (pullback.fst (ι i) (ι j) ≫ f' i) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B i))) =
      (pullback.snd (ι i) (ι j) ≫ f' j) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B j))) := by
    rw [Category.assoc, Category.assoc, ← (hsq i).w, ← (hsq j).w, ← Category.assoc, ← Category.assoc, pullback.condition]
  let fP := hbot.lift _ _ hw
  have hfP₁ : fP ≫ Spec.map (CommRingCat.ofHom ρ₁.toRingHom) = pullback.fst (ι i) (ι j) ≫ f' i := hbot.lift_fst _ _ hw
  have hfP₂ : fP ≫ Spec.map (CommRingCat.ofHom ρ₂.toRingHom) = pullback.snd (ι i) (ι j) ≫ f' j := hbot.lift_snd _ _ hw
  have hs : IsPullback (pullback.fst (ι i) (ι j)) (fP ≫ Spec.map (CommRingCat.ofHom ρ₂.toRingHom))
    (f' i ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B i)))) (Spec.map (CommRingCat.ofHom (algebraMap S (B j)))) := by
    rw [hfP₂, ← (hsq i).w]
    apply hR1
  refine ⟨ρ₁, fP, hawayI, IsPullback.of_bot hs hfP₁.symm hbot, ?_⟩
  have halg : algebraMap S (Localization.Away (r i * r j)) = ρ₁.toRingHom.comp (algebraMap S (B i)) :=
    RingHom.ext fun s => (ρ₁.commutes s).symm
  rw [halg, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc, hfP₁, Category.assoc, ← (hsq i).w]


-- created on 2026-10-20
