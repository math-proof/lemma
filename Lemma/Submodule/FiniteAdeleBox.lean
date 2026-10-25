import Mathlib
import Def.Submodule_FiniteAdeleBox

set_option autoImplicit false

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace Submodule

variable {D : Type*} [Ring D] [Algebra ℚ D]


@[simp] theorem val_finiteIdeleDiagonal_apply (d : Dˣ) :
    ((finiteIdeleDiagonal D d : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = (d : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl

theorem mem_ofFiniteIdele_iff (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (z : D) :
    z ∈ ofFiniteIdele Λ g ↔
      z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        (finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Iff.rfl

theorem mem_conjByFiniteIdele_iff (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (z : D) :
    z ∈ conjByFiniteIdele Λ g ↔
      z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        (finiteAdeleBox Λ).map
          ((AddMonoidHom.mulRight ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
              D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
            (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) :=
  Iff.rfl

theorem mem_finiteIdeleStabilizer_iff (Λ : Submodule ℤ D) (u : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    u ∈ finiteIdeleStabilizer Λ ↔
      u • ((finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))
        = ((finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Iff.rfl

end Submodule

end
