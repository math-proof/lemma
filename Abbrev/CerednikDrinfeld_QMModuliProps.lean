import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Structure.CerednikDrinfeld_QMModuli
import Structure.CerednikDrinfeld_QMModuliProps

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]


abbrev WithExtraLevel (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) (S : Type u) [CommRing S] : Type (u + 1) :=
  Σ E : FakeEllipticCurve Λ N S, E.ExtraLevel ℓ

end CerednikDrinfeld.QM.FakeEllipticCurve

namespace CerednikDrinfeld

open CerednikDrinfeld.QM

variable {a b : ℚ}

end CerednikDrinfeld

end
