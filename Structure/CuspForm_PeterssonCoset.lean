import Mathlib
import Def.AutomorphicForm_ModularFundamentalDomain
import Def.CuspForm_PeterssonCoset

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter CongruenceSubgroup
open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace CuspForm.PeterssonCoset


section weight

variable (Λ : Subgroup SL(2, ℤ))


variable [Fintype (SL(2, ℤ) ⧸ Λ)]


end weight

section cvn

variable (Λ₁ Λ₂ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Λ₁)] [Fintype (SL(2, ℤ) ⧸ Λ₂)]


end cvn

section pairing


structure Nice (Λ : Subgroup SL(2, ℤ)) (k : ℤ) (H : ℍ → ℂ) : Prop where
  cont : Continuous H
  bdd : ∃ C, ∀ x, dens k H x ≤ C
  inv : ∀ h ∈ Λ, H ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ h : GL (Fin 2) ℝ) = H

variable {Λ : Subgroup SL(2, ℤ)} {k : ℤ}


variable (Λ) [Fintype (SL(2, ℤ) ⧸ Λ)]


end pairing

section definite

variable (Λ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Λ)] {k : ℤ}


end definite

section level

variable {Γ'' Λ : Subgroup SL(2, ℤ)}

section unfold

variable (hΛΓ : Λ ≤ Γ'') {ι : Type*} (r : ι → SL(2, ℤ)) (hr : ∀ i, r i ∈ Γ'')
  (hex : ∀ γ ∈ Γ'', ∃ i, r i * γ ∈ Λ) (huniq : ∀ i i', r i * (r i')⁻¹ ∈ Λ → i = i')


include hΛΓ hr hex huniq in

variable [Fintype (SL(2, ℤ) ⧸ Γ'')] [Fintype (SL(2, ℤ) ⧸ Λ)] [Fintype ι]

include hΛΓ hr hex huniq in


end unfold

variable [Fintype (SL(2, ℤ) ⧸ Γ'')] [Fintype (SL(2, ℤ) ⧸ Λ)]


end level

section indexeq

variable (Λ₁ Λ₂ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Λ₁)] [Fintype (SL(2, ℤ) ⧸ Λ₂)]


end indexeq

end CuspForm.PeterssonCoset

end
