import Mathlib
import Lemma.AlgebraicCurve.Correspondence
import Def.AlgebraicCurve_Differentials

set_option autoImplicit false

noncomputable section

namespace ModularCurve.IgusaCover

open AlgebraicCurve

variable {κ : Type*} [Field κ] {Ω : Type*} [Field Ω] [Algebra κ Ω]

def igusaFunctionField (K₀ : IntermediateField κ Ω) (a : Ω) : IntermediateField κ Ω :=
  IntermediateField.adjoin κ ((K₀ : Set Ω) ∪ {a})

variable (K₀ : IntermediateField κ Ω) (a : Ω)


theorem mem_igusaFunctionField : a ∈ igusaFunctionField K₀ a :=
  IntermediateField.subset_adjoin κ _ (Or.inr rfl)


structure IsKummerGenerator (n : ℕ) (K₀ : IntermediateField κ Ω) (a : Ω) : Prop where

  pos : 0 < n
  ne_zero : a ≠ 0
  pow_mem : a ^ n ∈ K₀


structure IgusaDiamondData (p : ℕ) [Fact p.Prime] [CharP κ p] (k : ℤ) (K₀ : IntermediateField κ Ω) (a : Ω) where

  act : (ZMod p)ˣ →* (igusaFunctionField K₀ a ≃ₐ[κ] igusaFunctionField K₀ a)

  act_apply_of_mem : ∀ (b : (ZMod p)ˣ) (x : igusaFunctionField K₀ a), (x : Ω) ∈ K₀ → act b x = x

  act_gen : ∀ b : (ZMod p)ˣ,
    ((act b ⟨a, mem_igusaFunctionField K₀ a⟩ : igusaFunctionField K₀ a) : Ω) =
      (ZMod.castHom (dvd_refl p) κ (((b ^ k : (ZMod p)ˣ) : ZMod p))) • a

namespace IgusaDiamondData

variable {K₀ a} {p : ℕ} [Fact p.Prime] [CharP κ p] {k : ℤ}


end IgusaDiamondData

end ModularCurve.IgusaCover

end
