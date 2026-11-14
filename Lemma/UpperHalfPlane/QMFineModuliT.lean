import Structure.CerednikDrinfeld_QMFineModuli
import Def.CerednikDrinfeld_QMFormalModuleOf
import Def.CerednikDrinfeld_QMFineModuliT
import Structure.CerednikDrinfeld_QMFineModuliT

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace CerednikDrinfeld.QM

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}


theorem WithFullLevel.iso_iff_exists_via {S : Type} [CommRing S] {n : ℕ} (u u' : WithFullLevel Λ N n S) :
    WithFullLevel.Iso u u' ↔ ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), WithFullLevel.IsoVia u u' i hi := Iff.rfl


theorem WithFullLevel.isTwist_iff_exists_via {S : Type} [CommRing S] {n : ℕ} (c : ↥Λ) (u u' : WithFullLevel Λ N n S) :
    WithFullLevel.IsTwist c u u' ↔ ∃ (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f), WithFullLevel.IsTwistVia c u u' e he :=
  Iff.rfl

end FakeEllipticCurve

variable {a b : ℚ}


end CerednikDrinfeld.QM
