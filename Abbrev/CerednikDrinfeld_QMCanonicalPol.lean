import Structure.CerednikDrinfeld_QMFineModuli
import Structure.AlgebraicGeometry_PolarisedAbelianScheme
import Def.AlgebraicGeometry_PolarisationRosati

set_option autoImplicit false

noncomputable section

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u v


abbrev CerednikDrinfeld.QM.FakeEllipticCurve.IsCanonicalPol
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (star : ↥Λ → ↥Λ) (𝓛 : E.A.Modules) : Prop :=
  CerednikDrinfeld.QM.IsCanonicalPolData E.f E.L E.act E.act_over star 𝓛

end
