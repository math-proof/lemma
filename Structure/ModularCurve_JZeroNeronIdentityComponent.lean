import Mathlib
import Structure.ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Structure.AlgebraicGeometry_RelativeGroupLaw
import Lemma.GoodReductionJacobian.RelativeGroupLawKernel
import Lemma.AlgebraicGeometry.NeronModelEndomorphismExtension

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra
  GoodReductionJacobian

noncomputable section

namespace ModularCurve

structure JZeroNeronIdentityComponent (p : ℕ) [Fact p.Prime] where

  G : Scheme.{0}

  g : G ⟶ Spec (CommRingCat.of ℤ)

  L : RelativeGroupLaw ℤ g

  pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) g

  comm : L.IsCommutative

  smooth : Smooth g
  separated : IsSeparated g
  locallyOfFiniteType : LocallyOfFiniteType g
  quasiCompact : QuasiCompact g
  surjective : Surjective g
  fibre_preconnected : ∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (g.base ⁻¹' {s})

  pts_add : ∀ x y : JZero p, pts (x + y) = L.mul _ (pts x) (pts y)

  pts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
    (pts (σ • x)).1 =
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1

  hecke : letI := heckeModuleBar p
    ∀ t : HeckeAlg, ∃ φ : SchemeHomOver g g,
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver s g),
        NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
          L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JZero p, (pts (t • x)).1 = (pts x).1 ≫ φ.1

  nsmul_flat : ∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n)
  nsmul_surjective : ∀ n : ℕ, 0 < n → Surjective (L.schemeNsmul n)

  sections_finiteIndex :
    ((AddSubgroup.closure (Set.range fun s : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) g =>
        pts.symm (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
          (Category.comp_id _) s))).addSubgroupOf
      (FixedPoints.addSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero p))).FiniteIndex

  torsion_over_p : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p → ∀ m : ℕ, ¬ p ∣ m →
    {x : JZero p | x ∈ jZeroTorsion p m ∧
        ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g,
          (pts x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1}
      = (jZeroToricTorsion p A m : Set (JZero p))

  proper_away : IsProper (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ))))))

end ModularCurve

end
