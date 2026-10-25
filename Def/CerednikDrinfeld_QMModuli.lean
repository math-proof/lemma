import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Topology.KrullDimension
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Trace
import Structure.JacJ1Iface
import Lemma.AlgebraicGeometry.RelativeGroupLaw
import Lemma.CerednikDrinfeld.ShimuraCurve
import Structure.CerednikDrinfeld_QMModuli
import Abbrev.CerednikDrinfeld_QMModuli

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld.QM

section Points

variable {R : Type u} [CommRing R]


@[simp] theorem mapPt_coe {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    (mapPt φ hφ P).1 = P.1 ≫ φ := rfl


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


def ShimuraCurveModel.IsModuliModel {R₀ : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (M : ShimuraCurveModel R₀ ι 𝒮) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N q q' : ℕ) : Prop :=
  Nonempty (M.ModuliWitness Λ N q q')

end CerednikDrinfeld

end
