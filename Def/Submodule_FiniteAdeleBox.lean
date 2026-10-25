import Mathlib

set_option autoImplicit false

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace Submodule

variable {D : Type*} [Ring D] [Algebra ℚ D]

def finiteAdeleBox (Λ : Submodule ℤ D) : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  AddSubgroup.closure
    {x | ∃ z ∈ Λ, ∃ a : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] a}

def ofFiniteIdele (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Submodule ℤ D :=
  (AddSubgroup.toIntSubmodule
      ((finiteAdeleBox Λ).map
        (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)))).comap
    ((Algebra.TensorProduct.includeLeft :
        D →ₐ[ℚ] D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ).toLinearMap.restrictScalars ℤ)

def finiteIdeleStabilizer (Λ : Submodule ℤ D) : Subgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  MulAction.stabilizer (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ
    ((finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))

def conjByFiniteIdele (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule ℤ D :=
  (AddSubgroup.toIntSubmodule
      ((finiteAdeleBox Λ).map
        ((AddMonoidHom.mulRight ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
          (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))))).comap
    ((Algebra.TensorProduct.includeLeft :
        D →ₐ[ℚ] D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ).toLinearMap.restrictScalars ℤ)

variable (D) in

def finiteIdeleDiagonal : Dˣ →* (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeftRingHom :
    D →+* D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ).toMonoidHom

end Submodule

end
