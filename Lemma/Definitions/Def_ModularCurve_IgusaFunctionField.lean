import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
import Lemma.Definitions.Def_AlgebraicCurve_Differentials

set_option autoImplicit false

noncomputable section

namespace ModularCurve.IgusaCover

open AlgebraicCurve

variable {κ : Type*} [Field κ] {Ω : Type*} [Field Ω] [Algebra κ Ω]

def igusaFunctionField (K₀ : IntermediateField κ Ω) (a : Ω) : IntermediateField κ Ω :=
  IntermediateField.adjoin κ ((K₀ : Set Ω) ∪ {a})

variable (K₀ : IntermediateField κ Ω) (a : Ω)

theorem le_igusaFunctionField : K₀ ≤ igusaFunctionField K₀ a :=
  fun _ hx => IntermediateField.subset_adjoin κ _ (Or.inl hx)

theorem mem_igusaFunctionField : a ∈ igusaFunctionField K₀ a :=
  IntermediateField.subset_adjoin κ _ (Or.inr rfl)

theorem igusaFunctionField_eq_sup :
    igusaFunctionField K₀ a = K₀ ⊔ IntermediateField.adjoin κ {a} := by
  rw [igusaFunctionField, IntermediateField.adjoin_union, IntermediateField.adjoin_self]

def incl : K₀ →ₐ[κ] igusaFunctionField K₀ a :=
  IntermediateField.inclusion (le_igusaFunctionField K₀ a)

@[simp] theorem coe_incl (x : K₀) : ((incl K₀ a x : igusaFunctionField K₀ a) : Ω) = x := rfl

def qExpansion : igusaFunctionField K₀ a →ₐ[κ] Ω := (igusaFunctionField K₀ a).val

theorem qExpansion_incl (x : K₀) : qExpansion K₀ a (incl K₀ a x) = (x : Ω) := rfl

structure IsKummerGenerator (n : ℕ) (K₀ : IntermediateField κ Ω) (a : Ω) : Prop where

  pos : 0 < n
  ne_zero : a ≠ 0
  pow_mem : a ^ n ∈ K₀

def restrictToBase (hint : (incl K₀ a).toRingHom.IsIntegral) (w : Place κ (igusaFunctionField K₀ a)) : Place κ K₀ :=
  w.restrictAlong (incl K₀ a) hint

def ramificationIndexOverBase (w : Place κ (igusaFunctionField K₀ a)) : ℕ :=
  w.ramificationIndexAlong (incl K₀ a)

structure IgusaDiamondData (p : ℕ) [Fact p.Prime] [CharP κ p] (k : ℤ) (K₀ : IntermediateField κ Ω) (a : Ω) where

  act : (ZMod p)ˣ →* (igusaFunctionField K₀ a ≃ₐ[κ] igusaFunctionField K₀ a)

  act_apply_of_mem : ∀ (b : (ZMod p)ˣ) (x : igusaFunctionField K₀ a), (x : Ω) ∈ K₀ → act b x = x

  act_gen : ∀ b : (ZMod p)ˣ,
    ((act b ⟨a, mem_igusaFunctionField K₀ a⟩ : igusaFunctionField K₀ a) : Ω) =
      (ZMod.castHom (dvd_refl p) κ (((b ^ k : (ZMod p)ˣ) : ZMod p))) • a

namespace IgusaDiamondData

variable {K₀ a} {p : ℕ} [Fact p.Prime] [CharP κ p] {k : ℤ}

def actDiff (d : IgusaDiamondData p k K₀ a) (b : (ZMod p)ˣ) :
    Ω[igusaFunctionField K₀ a⁄κ] →ₗ[κ] Ω[igusaFunctionField K₀ a⁄κ] :=
  pullbackDiff (d.act b : igusaFunctionField K₀ a →ₐ[κ] igusaFunctionField K₀ a)

theorem act_incl (d : IgusaDiamondData p k K₀ a) (b : (ZMod p)ˣ) (x : K₀) : d.act b (incl K₀ a x) = incl K₀ a x :=
  d.act_apply_of_mem b _ x.2

end IgusaDiamondData

end ModularCurve.IgusaCover

end
