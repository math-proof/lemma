import Mathlib.Algebra.CharP.Frobenius
import Structure.CerednikDrinfeld_QMModuliProps

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

structure FrobeniusVerschiebungData (ℓ : ℕ) [Fact ℓ.Prime] [CharP S ℓ] (E Eℓ : FakeEllipticCurve Λ N S) : Type u where

  pr : Eℓ.A ⟶ E.A

  pr_isPullback : CategoryTheory.IsPullback pr Eℓ.f E.f (Spec.map (CommRingCat.ofHom (frobenius S ℓ)))

  pr_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t' Eℓ.f),
    (Eℓ.L.mul t' P Q).1 ≫ pr =
      (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (frobenius S ℓ)))
        ⟨P.1 ≫ pr, by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pr, by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, Q.2]⟩).1

  pr_act : ∀ x : ↥Λ, Eℓ.act x ≫ pr = pr ≫ E.act x

  pr_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t' Eℓ.f),
    FactorsThrough Eℓ.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ pr

  F : E.A ⟶ Eℓ.A

  F_over : F ≫ Eℓ.f = E.f

  V : Eℓ.A ⟶ E.A

  V_over : V ≫ E.f = Eℓ.f

  F_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
    mapPt F F_over (E.L.mul t P Q) = Eℓ.L.mul t (mapPt F F_over P) (mapPt F F_over Q)

  V_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t Eℓ.f),
    mapPt V V_over (Eℓ.L.mul t P Q) = E.L.mul t (mapPt V V_over P) (mapPt V V_over Q)

  F_act : ∀ x : ↥Λ, E.act x ≫ F = F ≫ Eℓ.act x

  V_act : ∀ x : ↥Λ, Eℓ.act x ≫ V = V ≫ E.act x

  F_lev : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    FactorsThrough E.lev P → FactorsThrough Eℓ.lev (mapPt F F_over P)

  V_lev : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t Eℓ.f),
    FactorsThrough Eℓ.lev P → FactorsThrough E.lev (mapPt V V_over P)

  V_F : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    mapPt V V_over (mapPt F F_over P) = nsmulPt E.L t ℓ P

  F_V : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t Eℓ.f),
    mapPt F F_over (mapPt V V_over Q) = nsmulPt Eℓ.L t ℓ Q

  F_frobenius : ∀ (B : Type u) [CommRing B] [CharP B ℓ] (x : Spec (CommRingCat.of B) ⟶ E.A),
    x ≫ F ≫ pr = Spec.map (CommRingCat.ofHom (frobenius B ℓ)) ≫ x

namespace FrobeniusVerschiebungData

variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP S ℓ] {E Eℓ : FakeEllipticCurve Λ N S}


end FrobeniusVerschiebungData


end CerednikDrinfeld.QM.FakeEllipticCurve

end
