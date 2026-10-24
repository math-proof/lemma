import Mathlib
import Lemma.Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Lemma.Definitions.Def_ModularCurve_ReductionModL
import Lemma.Definitions.Def_JacJ1Iface
import Lemma.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Lemma.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Lemma.Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Lemma.Definitions.Def_ModularCurve_ArithmeticGalois
import Lemma.Definitions.Def_ModularCurve_HeckeModule
import Lemma.Definitions.Def_FLTPrelim_Ramification
import Lemma.Definitions.Def_GaloisRep_Flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing

noncomputable section

namespace ModularCurve

structure JZeroNeronIdentityComponent.GoodPrimeData (p : ℕ) [Fact p.Prime]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) (L : RelativeGroupLaw ℤ g)
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) g)
    (ℓ : ℕ) [Fact ℓ.Prime] where

  L' : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt ℓ) (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))))

  pts' : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
    (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))))

  law_compat : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
    (x y : SchemeHomOver t (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))))
    (X Y : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) g),
    X.1 = x.1 ≫ pullback.fst _ _ → Y.1 = y.1 ≫ pullback.fst _ _ →
    (L'.mul t x y).1 ≫ pullback.fst _ _ = (L.mul _ X Y).1

  pts_compat : ∀ x : JZero p, (pts' x).1 ≫ pullback.fst _ _ = (pts x).1

  bundle : AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ) (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))))

  comm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
    (x y : SchemeHomOver t (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))))), L'.mul t x y = L'.mul t y x

  pts_add : ∀ x y : JZero p, pts' (x + y) = L'.mul _ (pts' x) (pts' y)

  pts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
    (pts' (σ • x)).1 =
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts' x).1

  pointsDict : ∀ (A' : ValuationSubring (AlgebraicClosure ℚ)), A'.LiesOverPrime ℓ →
    ∃ (σA : Spec (CommRingCat.of ↥A') ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
      (ptsA : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom A'.subtype) ≫ σA) (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))))
      (ptsSp : JZeroC (ResidueField ↥A') p ≃
        SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A')) ≫ σA) (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))))),
      (∀ x : JZero p, (ptsA x).1 = (pts' x).1) ∧
      (∀ u v : JZeroC (ResidueField ↥A') p, ptsSp (u + v) = L'.mul _ (ptsSp u) (ptsSp v)) ∧
      (ReductionInputsModL A' p → ReductionOfPointsAgreesModL p A' (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))) σA ptsA ptsSp)

  hecke : letI := heckeModuleBar p
    ∀ t : HeckeAlg, ∃ φ : SchemeHomOver (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))) (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))),
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x y : SchemeHomOver s (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))))),
        NeronModelInfra.schemeHomOverComp (L'.mul s x y) φ =
          L'.mul s (NeronModelInfra.schemeHomOverComp x φ)
            (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JZero p, (pts' (t • x)).1 = (pts' x).1 ≫ φ.1

structure JZeroNeronIdentityComponentGood (p : ℕ) [Fact p.Prime] extends JZeroNeronIdentityComponent p where

  goodPrime : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ p →
    JZeroNeronIdentityComponent.GoodPrimeData p g L pts ℓ

end ModularCurve

end
