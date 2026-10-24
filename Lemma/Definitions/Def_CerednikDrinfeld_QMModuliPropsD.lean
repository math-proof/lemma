import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Lemma.Definitions.Def_CerednikDrinfeld_QMModuliWitnessD
import Lemma.Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld

open CerednikDrinfeld.QM

variable {a b : ℚ}

def ShimuraCurveModel.ModuliWitnessD.IsOriented {R₀ : Submodule ℤ ℍ[ℚ, a, b]}
    {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    {M : ShimuraCurveModel R₀ ι 𝒮} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N q q' D : ℕ}
    (w : M.ModuliWitnessD Λ N q q' D) : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∣ N → ∀ (P Q : Place (AlgebraicClosure ℚ) M.Fbar),
    Q ∈ (M.corrBar ℓ hℓ (Finsupp.single P 1)).support ↔
      ∃ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) (d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
        w.pt _ w.sbar u.1 = w.pts P ∧ w.pt _ w.sbar d = w.pts Q ∧ FakeEllipticCurve.IsLevelIsogeny ℓ u d

def ShimuraCurveModel.ModuliWitnessD.IsGoodReductionModel {R₀ : Submodule ℤ ℍ[ℚ, a, b]}
    {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    {M : ShimuraCurveModel R₀ ι 𝒮} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N q q' D : ℕ}
    (w : M.ModuliWitnessD Λ N q q' D) : Prop :=
  SmoothOfRelativeDimension 1 w.πX ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
    IsIntegral (CategoryTheory.Limits.pullback w.πX s)

end CerednikDrinfeld

end
