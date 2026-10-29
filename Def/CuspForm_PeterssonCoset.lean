import Mathlib
import Def.AutomorphicForm_ModularFundamentalDomain

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter CongruenceSubgroup
open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace CuspForm.PeterssonCoset


section weight

variable (Λ : Subgroup SL(2, ℤ))

def splitEquiv : SL(2, ℤ) ≃ (SL(2, ℤ) ⧸ Λ) × Λ where
  toFun σ := (QuotientGroup.mk σ, ⟨(QuotientGroup.mk σ : SL(2, ℤ) ⧸ Λ).out⁻¹ * σ, by
    rw [← QuotientGroup.eq]; exact QuotientGroup.out_eq' _⟩)
  invFun x := x.1.out * x.2
  left_inv σ := by simp
  right_inv := by
    rintro ⟨q, h⟩
    have hq : (QuotientGroup.mk (q.out * (h : SL(2, ℤ))) : SL(2, ℤ) ⧸ Λ) = q := by
      rw [QuotientGroup.mk_mul_of_mem _ h.2, QuotientGroup.out_eq']
    refine Prod.ext hq (Subtype.ext ?_)
    simp only [hq]
    rw [inv_mul_cancel_left]


variable [Fintype (SL(2, ℤ) ⧸ Λ)]

def wt (x : ℍ) : ENNReal :=
  ∑ q : SL(2, ℤ) ⧸ Λ, (𝒟 : Set ℍ).indicator (fun _ => (1 : ENNReal)) ((q.out : SL(2, ℤ)) • x)

end weight


section pairing

def dens (k : ℤ) (H : ℍ → ℂ) (x : ℍ) : ℝ := ‖H x‖ ^ 2 * x.im ^ k


variable {Λ : Subgroup SL(2, ℤ)} {k : ℤ}


variable (Λ) [Fintype (SL(2, ℤ) ⧸ Λ)]

def cosum (g : GL (Fin 2) ℝ) (Φ : ℍ → ℂ) (x : ℍ) : ℂ :=
  ∑ q : SL(2, ℤ) ⧸ Λ, Φ (g • (q.out⁻¹ : SL(2, ℤ)) • x)

def pair (k : ℤ) (F G : ℍ → ℂ) : ℂ :=
  ∫ x in (𝒟 : Set ℍ), cosum Λ 1 (UpperHalfPlane.petersson k F G) x

end pairing


section level

variable {Γ'' Λ : Subgroup SL(2, ℤ)}

section unfold

variable (hΛΓ : Λ ≤ Γ'') {ι : Type*} (r : ι → SL(2, ℤ)) (hr : ∀ i, r i ∈ Γ'')
  (hex : ∀ γ ∈ Γ'', ∃ i, r i * γ ∈ Λ) (huniq : ∀ i i', r i * (r i')⁻¹ ∈ Λ → i = i')

def eMap (r : ι → SL(2, ℤ)) (x : (SL(2, ℤ) ⧸ Γ'') × ι) : SL(2, ℤ) ⧸ Λ :=
  QuotientGroup.mk (x.1.out * (r x.2)⁻¹)

end unfold

end level

end CuspForm.PeterssonCoset

end
