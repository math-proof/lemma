import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Topology.KrullDimension
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Trace
import Structure.JacJ1Iface
import Structure.AlgebraicGeometry_RelativeGroupLaw
import Instance.CerednikDrinfeld_ShimuraCurve
import Structure.CerednikDrinfeld_QMModuli

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld.QM

section Points

variable {R : Type u} [CommRing R]


abbrev pushPt {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A) (hφ : φ ≫ f = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) : SchemeHomOver t f :=
  mapPt φ hφ P


end Points

section Tangent

variable {S : Type u} [CommRing S]


end Tangent

variable {a b : ℚ}


namespace FakeEllipticCurve

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}


end FakeEllipticCurve

end CerednikDrinfeld.QM

namespace CerednikDrinfeld

open CerednikDrinfeld.QM

variable {a b : ℚ}


end CerednikDrinfeld

end
