import Lemma.Definitions.Def_CerednikDrinfeld_QMModuliPropsD
import Lemma.Definitions.Def_CerednikDrinfeld_QMModuliTower

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld.QM

variable {a b : ℚ}

structure ModuliTowerWitnessD (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N q q' D : ℕ) [Fact q.Prime] [Fact q'.Prime]
    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar) (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar)
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ)) : Type 1 where

  rep : Place (AlgebraicClosure ℚ) Fbar → FakeEllipticCurve Λ N (AlgebraicClosure ℚ)

  pt_rep : ∀ P : Place (AlgebraicClosure ℚ) Fbar,
    (pt _ sbar (rep P)).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar

  repT : ∀ ℓ : HeckeTower.AwayPrime q q',
    Place (AlgebraicClosure ℚ) (𝕋.F ℓ) → FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ)

  repT_surjective : ∀ (ℓ : HeckeTower.AwayPrime q q') (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ)),
    ∃ P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ), FakeEllipticCurve.WithExtraLevel.Iso (repT ℓ P) u

  repT_injective : ∀ (ℓ : HeckeTower.AwayPrime q q') (P Q : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.WithExtraLevel.Iso (repT ℓ P) (repT ℓ Q) → P = Q

  gal_base : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    SemilinearAut.baseAut (gal σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)

  galT_base : ∀ (ℓ : HeckeTower.AwayPrime q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
    SemilinearAut.baseAut (galT ℓ σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)

  W_base : ∀ (i : Fin 2) (c : AlgebraicClosure ℚ), SemilinearAut.baseAut (W i) c = c

  WT_base : ∀ (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2) (c : AlgebraicClosure ℚ), SemilinearAut.baseAut (WT ℓ i) c = c

  restrict_zero : ∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.IsLevelRestrict (repT ℓ P) (rep (P.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0))))

  restrict_one : ∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) (repT ℓ P) (rep (P.restrictAlong (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 1))))

  gal_rep : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : Place (AlgebraicClosure ℚ) Fbar),
    ∃ E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ),
      FakeEllipticCurve.IsPullback (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (rep P) E ∧
        FakeEllipticCurve.Iso E (rep (gal σ • P))

  galT_rep : ∀ (ℓ : HeckeTower.AwayPrime q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    ∃ (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ)) (g : u.1.A ⟶ (repT ℓ P).1.A)
      (hg : CategoryTheory.IsPullback g u.1.f (repT ℓ P).1.f
        (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q Q' : SchemeHomOver t' u.1.f),
        (u.1.L.mul t' Q Q').1 ≫ g =
          ((repT ℓ P).1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)))
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩
            ⟨Q'.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q'.2]⟩).1) ∧
      (∀ x : ↥Λ, u.1.act x ≫ g = g ≫ (repT ℓ P).1.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t' u.1.f),
        (FactorsThrough u.1.lev Q → ∃ Q₀ : T ⟶ (repT ℓ P).1.C, Q₀ ≫ (repT ℓ P).1.lev = Q.1 ≫ g) ∧
        (FactorsThrough u.2.levK Q → ∃ Q₀ : T ⟶ (repT ℓ P).2.K, Q₀ ≫ (repT ℓ P).2.levK = Q.1 ≫ g)) ∧
      FakeEllipticCurve.WithExtraLevel.Iso u (repT ℓ (galT ℓ σ • P))

  W_zero_rep : ∀ P : Place (AlgebraicClosure ℚ) Fbar, (rep P).IsAtkinLehnerQuotient q (rep (W 0 • P))

  W_one_rep : ∀ P : Place (AlgebraicClosure ℚ) Fbar, (rep P).IsAtkinLehnerQuotient q' (rep (W 1 • P))

  WT_zero_rep : ∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient q (repT ℓ P) (repT ℓ (WT ℓ 0 • P))

  WT_one_rep : ∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient q' (repT ℓ P) (repT ℓ (WT ℓ 1 • P))

end CerednikDrinfeld.QM

end
