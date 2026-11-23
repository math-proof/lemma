import Lemma.Matrix.ConductorDatum
import Instance.LocalNewvector_PrincipalSeriesCarrier

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

variable (p : ℕ) [Fact p.Prime]

section BorelElements

def borelElem (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) : GL (Fin 2) ℚ_[p] :=
  ⟨!![(a₁ : ℚ_[p]), x; 0, (a₂ : ℚ_[p])],
   !![((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]), -(((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * x * ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p]));
      0, ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p])],
   by
    have h1 : (a₁ : ℚ_[p]) ≠ 0 := a₁.ne_zero
    have h2 : (a₂ : ℚ_[p]) ≠ 0 := a₂.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val, mul_assoc, h1, h2],
   by
    have h1 : (a₁ : ℚ_[p]) ≠ 0 := a₁.ne_zero
    have h2 : (a₂ : ℚ_[p]) ≠ 0 := a₂.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val, mul_assoc, h1, h2]⟩

end BorelElements

section HalfModulus

def halfModulus (a₁ a₂ : ℚ_[p]ˣ) : ℂ :=
  (Real.sqrt (‖(a₁ : ℚ_[p])‖ / ‖(a₂ : ℚ_[p])‖) : ℝ)

end HalfModulus

section PrincipalSeries

def principalSeries (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) : Submodule ℂ (GL (Fin 2) ℚ_[p] → ℂ) where
  carrier := {f | IsLocallyConstant f ∧
    ∀ (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (g : GL (Fin 2) ℚ_[p]),
      f (borelElem p a₁ a₂ x * g)
        = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ * f g}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun a₁ a₂ x g => by simp⟩
  add_mem' := by
    intro f g hf hg
    obtain ⟨hf_lc, hf_tr⟩ := hf
    obtain ⟨hg_lc, hg_tr⟩ := hg
    refine ⟨hf_lc.comp₂ hg_lc (· + ·), fun a₁ a₂ x g₀ => ?_⟩
    show f _ + g _ = _ * (f g₀ + g g₀)
    rw [hf_tr, hg_tr]
    ring
  smul_mem' := by
    intro c f hf
    obtain ⟨hf_lc, hf_tr⟩ := hf
    refine ⟨hf_lc.comp (c * ·), fun a₁ a₂ x g₀ => ?_⟩
    show c * f _ = _ * (c * f g₀)
    rw [hf_tr]
    ring

end PrincipalSeries

section RightInvariant

def rightInvariantFunctions (U : Subgroup (GL (Fin 2) ℚ_[p])) :
    Submodule ℂ (GL (Fin 2) ℚ_[p] → ℂ) where
  carrier := {f | ∀ u ∈ U, ∀ x, f (x * u) = f x}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := by
    intro f g hf hg u hu x
    show f (x * u) + g (x * u) = f x + g x
    rw [hf u hu x, hg u hu x]
  smul_mem' := by
    intro c f hf u hu x
    show c * f (x * u) = c * f x
    rw [hf u hu x]

end RightInvariant

section PrincipalSeriesCarrier

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

def PSCarrier : Type := ↥(principalSeries p μ₁ μ₂)

namespace PSCarrier

def mk (f : ↥(principalSeries p μ₁ μ₂)) : PSCarrier p μ₁ μ₂ := f

def toSub (f : PSCarrier p μ₁ μ₂) : ↥(principalSeries p μ₁ μ₂) := f

def toFn (f : PSCarrier p μ₁ μ₂) : GL (Fin 2) ℚ_[p] → ℂ :=
  (toSub p μ₁ μ₂ f : GL (Fin 2) ℚ_[p] → ℂ)

def toSubEquiv : PSCarrier p μ₁ μ₂ ≃ₗ[ℂ] ↥(principalSeries p μ₁ μ₂) where
  toFun := toSub p μ₁ μ₂
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := mk p μ₁ μ₂
  left_inv _ := rfl
  right_inv _ := rfl

def fixedEquiv (U : Subgroup (GL (Fin 2) ℚ_[p])) :
    ↥(LocalNewvector.fixedSubmodule U (PSCarrier p μ₁ μ₂)) ≃ₗ[ℂ]
      ↥(principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p U) where
  toFun v := ⟨toFn p μ₁ μ₂ v.val, Submodule.mem_inf.mpr
    ⟨toFn_mem p μ₁ μ₂ v.val, by
      rw [mem_rightInvariantFunctions_iff]
      intro u hu y
      exact congrArg (fun z => toFn p μ₁ μ₂ z y)
        ((LocalNewvector.mem_fixedSubmodule_iff.mp v.property) u hu)⟩⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  invFun w := ⟨mk p μ₁ μ₂ ⟨w.val, (Submodule.mem_inf.mp w.property).1⟩, by
    rw [LocalNewvector.mem_fixedSubmodule_iff]
    intro u hu
    refine ext p μ₁ μ₂ fun y => ?_
    exact (mem_rightInvariantFunctions_iff p).mp
      (Submodule.mem_inf.mp w.property).2 u hu y⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

end PSCarrier

end PrincipalSeriesCarrier

end LocalNewvector

end
