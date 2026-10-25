import Def.CerednikDrinfeld_QMModuli
import Structure.CerednikDrinfeld_QMLatticeAction

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion

namespace CerednikDrinfeld.QM

variable {a b : ℚ}


namespace LatticeAction

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]}

@[ext] theorem ext {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    {X Y : LatticeAction Λ f L} (h : X.act = Y.act) : X = Y := by
  cases X; cases Y; cases h; rfl

def ofFakeEllipticCurve {N : ℕ} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) : LatticeAction Λ E.f E.L where
  act := E.act
  act_over := E.act_over
  act_hom := E.act_hom
  act_one := E.act_one
  act_mul := E.act_mul
  act_add := E.act_add

@[simp] theorem ofFakeEllipticCurve_act {N : ℕ} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) :
    (ofFakeEllipticCurve E).act = E.act := rfl

end LatticeAction


end CerednikDrinfeld.QM

end
