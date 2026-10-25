import Mathlib
import Lemma.Submodule.FiniteAdeleBox
import Def.QuaternionAlgebra_Order_FiniteIdele
import Instance.Submodule_LocalBox
import Def.Submodule_LocalBox

set_option autoImplicit false

open scoped TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField

noncomputable section


namespace Submodule

variable {D : Type*} [Ring D] [Algebra ℚ D]


@[simp] theorem finiteAdeleEvalAt_tmul (v : HeightOneSpectrum (𝓞 ℚ)) (z : D)
    (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    finiteAdeleEvalAt D v (z ⊗ₜ[ℚ] a) = z ⊗ₜ[ℚ] (a v) := rfl

theorem finiteAdeleEvalAlgHom_apply (v : HeightOneSpectrum (𝓞 ℚ)) (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    finiteAdeleEvalAlgHom v a = a v := rfl

theorem mem_localBoxUnits_iff (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))
    (u : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    u ∈ localBoxUnits Λ v ↔
      (u : D ⊗[ℚ] v.adicCompletion ℚ) ∈ (localBox Λ v : Set (D ⊗[ℚ] v.adicCompletion ℚ)) ∧
        ((u⁻¹ : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ)
          ∈ (localBox Λ v : Set (D ⊗[ℚ] v.adicCompletion ℚ)) :=
  Iff.rfl

end Submodule

namespace QuaternionAlgebra

variable {a b : ℚ}


theorem mem_localQuadUnits_iff (α : ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ))
    (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    u ∈ localQuadUnits α v ↔
      (u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ localQuadSubring α v ∧
        ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
          ∈ localQuadSubring α v :=
  Iff.rfl

theorem mem_localEmbeddingSet_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b])
    (v : HeightOneSpectrum (𝓞 ℚ)) (β : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    β ∈ localEmbeddingSet Λ α v ↔
      ∀ y ∈ localQuadSubring α v,
        ((β⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * y * β
            ∈ (Submodule.localBox Λ v : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
          ↔ y ∈ (Submodule.localBox Λ v : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) :=
  Iff.rfl

end QuaternionAlgebra

end
