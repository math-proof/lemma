import Mathlib
import Def.Submodule_FiniteAdeleBox
import Def.QuaternionAlgebra_Order_FiniteIdele
import Instance.Submodule_LocalBox

set_option autoImplicit false

open scoped TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField

noncomputable section


namespace Submodule

variable {D : Type*} [Ring D] [Algebra ℚ D]

variable (D) in

def finiteAdeleEvalAlgHom (v : HeightOneSpectrum (𝓞 ℚ)) :
    FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] v.adicCompletion ℚ :=
  { RestrictedProduct.evalRingHom
      (fun w : HeightOneSpectrum (𝓞 ℚ) => w.adicCompletion ℚ) v with
    commutes' := fun _ => rfl }

variable (D) in

def finiteAdeleEvalAt (v : HeightOneSpectrum (𝓞 ℚ)) :
    D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] D ⊗[ℚ] v.adicCompletion ℚ :=
  Algebra.TensorProduct.map (AlgHom.id ℚ D) (finiteAdeleEvalAlgHom v)

def localBox (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ)) :
    AddSubgroup (D ⊗[ℚ] v.adicCompletion ℚ) :=
  AddSubgroup.closure
    {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}

def localBoxUnits (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Set (D ⊗[ℚ] v.adicCompletion ℚ)ˣ :=
  {u | (u : D ⊗[ℚ] v.adicCompletion ℚ) ∈ (localBox Λ v : Set (D ⊗[ℚ] v.adicCompletion ℚ)) ∧
    ((u⁻¹ : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ)
      ∈ (localBox Λ v : Set (D ⊗[ℚ] v.adicCompletion ℚ))}

end Submodule

namespace QuaternionAlgebra

variable {a b : ℚ}

def localQuadSubring (α : ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Subring (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  Subring.closure
    ({α ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)} ∪
      Set.range (fun r : v.adicCompletion ℚ => (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r))

def localQuadUnits (α : ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ where
  carrier := {u | (u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ localQuadSubring α v ∧
    ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
      ∈ localQuadSubring α v}
  one_mem' :=
    ⟨by rw [Units.val_one]; exact (localQuadSubring α v).one_mem,
     by rw [inv_one, Units.val_one]; exact (localQuadSubring α v).one_mem⟩
  mul_mem' := fun {x y} hx hy =>
    ⟨by rw [Units.val_mul]; exact (localQuadSubring α v).mul_mem hx.1 hy.1,
     by rw [mul_inv_rev, Units.val_mul]; exact (localQuadSubring α v).mul_mem hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

def localEmbeddingSet (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ :=
  {β | ∀ y ∈ localQuadSubring α v,
    ((β⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * y * β
        ∈ (Submodule.localBox Λ v : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
      ↔ y ∈ (Submodule.localBox Λ v : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))}

end QuaternionAlgebra

end
