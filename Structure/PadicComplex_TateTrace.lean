import Mathlib
import Instance.PadicComplex_GaloisAction
import Def.PadicComplex_TateTrace

set_option autoImplicit false

noncomputable section

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]


structure IsTateTrace (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (m : ℕ) (d : ℝ)
    (R : ℂ_[p] → ℂ_[p]) : Prop where
  map_add : ∀ x ∈ towerClosure p Km, ∀ y ∈ towerClosure p Km, R (x + y) = R x + R y
  map_mul_left : ∀ (k : Km m), ∀ x ∈ towerClosure p Km,
    R (((k : PadicAlgCl p) : ℂ_[p]) * x) = ((k : PadicAlgCl p) : ℂ_[p]) * R x
  apply_coe : ∀ k : Km m, R ((k : PadicAlgCl p) : ℂ_[p]) = ((k : PadicAlgCl p) : ℂ_[p])
  exists_eq_coe : ∀ x ∈ towerClosure p Km, ∃ k : Km m, R x = ((k : PadicAlgCl p) : ℂ_[p])
  apply_smul : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (Km m).fixingSubgroup →
    ∀ x ∈ towerClosure p Km, R (σ • x) = R x
  norm_sub_apply_le : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (Km m).fixingSubgroup →
    σ ∉ (Km (m + 1)).fixingSubgroup → ∀ x ∈ towerClosure p Km, ‖x - R x‖ ≤ d * ‖σ • x - x‖

end PadicComplex

end
