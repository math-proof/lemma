import Mathlib
import Def.Submodule_FiniteAdeleBox
import Def.QuaternionAlgebra_Order

set_option autoImplicit false

open scoped TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace QuaternionAlgebra

variable {a b : ℚ}

def finiteAdeleQuadSubring (α : ℍ[ℚ, a, b]) : Subring (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  Subring.closure
    ({α ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)} ∪
      Set.range (fun r : FiniteAdeleRing (𝓞 ℚ) ℚ => (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r))

def finiteIdeleQuadUnits (α : ℍ[ℚ, a, b]) : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ where
  carrier := {u | (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ finiteAdeleQuadSubring α ∧
    ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ finiteAdeleQuadSubring α}
  one_mem' := ⟨by rw [Units.val_one]; exact one_mem _, by rw [inv_one, Units.val_one]; exact one_mem _⟩
  mul_mem' := fun {x y} hx hy =>
    ⟨by rw [Units.val_mul]; exact mul_mem hx.1 hy.1,
     by rw [mul_inv_rev, Units.val_mul]; exact mul_mem hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

def quadUnitsDiagonal (α : ℍ[ℚ, a, b]) : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range ⊓ finiteIdeleQuadUnits α

def embeddingSetOrd (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) :
    Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  {β | ∀ y ∈ finiteAdeleQuadSubring α,
    ((β⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * y * β
        ∈ (Submodule.finiteAdeleBox Λ : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))
      ↔ y ∈ (Submodule.finiteAdeleBox Λ : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))}

def IdelicEmbeddingClassSet (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) : Type :=
  {q : DoubleCoset.Quotient
      ((quadUnitsDiagonal α : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
      ((Submodule.finiteIdeleStabilizer Λ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) //
    ∃ x ∈ embeddingSetOrd Λ α,
      DoubleCoset.mk (quadUnitsDiagonal α) (Submodule.finiteIdeleStabilizer Λ) x = q}

def EmbeddingClassFibre (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b])
    (β : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Type :=
  {q : DoubleCoset.Quotient
      ((quadUnitsDiagonal α : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
      ((Submodule.finiteIdeleStabilizer Λ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) //
    ∃ x ∈ embeddingSetOrd Λ α,
      DoubleCoset.mk (quadUnitsDiagonal α) (Submodule.finiteIdeleStabilizer Λ) x = q ∧
      (DoubleCoset.mk (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range
          (Submodule.finiteIdeleStabilizer Λ) x :
        DoubleCoset.Quotient
          (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
          ((Submodule.finiteIdeleStabilizer Λ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ))
        = DoubleCoset.mk (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range
          (Submodule.finiteIdeleStabilizer Λ) β}

end QuaternionAlgebra

end
