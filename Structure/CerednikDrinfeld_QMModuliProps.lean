import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Structure.CerednikDrinfeld_QMModuli

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

structure ExtraLevel (E : FakeEllipticCurve Λ N S) (ℓ : ℕ) : Type (u + 1) where

  K : Scheme.{u}

  levK : K ⟶ E.A

  levK_closed : IsClosedImmersion levK

  levK_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
    FactorsThrough levK P → FactorsThrough levK Q → FactorsThrough levK (E.L.mul t P Q) ∧ FactorsThrough levK (E.L.inv t P)

  levK_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), FactorsThrough levK (E.L.one t)

  levK_torsion : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    FactorsThrough levK P → nsmulPt E.L t ℓ P = E.L.one t

  levK_stable : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    FactorsThrough levK P → FactorsThrough levK (pushPt (E.act x) (E.act_over x) P)

  levK_disjoint : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    FactorsThrough levK P → FactorsThrough E.lev P → P = E.L.one t

  levK_finite : IsFinite (levK ≫ E.f)

  levK_flat : Flat (levK ≫ E.f)

  levK_finitePresentation : LocallyOfFinitePresentation (levK ≫ E.f)

  levK_rank : ∀ s : ↥(Spec (CommRingCat.of S)), (levK ≫ E.f).finrank s = ℓ ^ 2

  levK_fibre : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k), (ℓ : k) ≠ 0 →
    ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough levK P},
      ∀ x y : ZMod ℓ × ZMod ℓ, (e (x + y) : SchemeHomOver (geomPoint k sk) E.f) = E.L.mul (geomPoint k sk) (e x) (e y)


end CerednikDrinfeld.QM.FakeEllipticCurve

namespace CerednikDrinfeld

open CerednikDrinfeld.QM

variable {a b : ℚ}


end CerednikDrinfeld

end
