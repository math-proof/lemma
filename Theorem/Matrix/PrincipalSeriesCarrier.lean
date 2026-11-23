module

public import Theorem.Matrix.ConductorDatum
public import Instance.LocalNewvector_PrincipalSeriesCarrier

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

variable (p : ℕ) [Fact p.Prime]

section BorelElements


@[simp] public theorem coe_borelElem (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    (borelElem p a₁ a₂ x : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = !![(a₁ : ℚ_[p]), x; 0, (a₂ : ℚ_[p])] :=
  rfl


@[simp] public theorem coe_borelElem_inv (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    (((borelElem p a₁ a₂ x)⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = !![((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]),
            -(((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * x * ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p]));
          0, ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p])] :=
  rfl


public theorem borelElem_mul (a₁ a₂ b₁ b₂ : ℚ_[p]ˣ) (x y : ℚ_[p]) :
    borelElem p a₁ a₂ x * borelElem p b₁ b₂ y
      = borelElem p (a₁ * b₁) (a₂ * b₂) ((a₁ : ℚ_[p]) * y + x * (b₂ : ℚ_[p])) := by
  apply Units.ext
  show (borelElem p a₁ a₂ x : Matrix (Fin 2) (Fin 2) ℚ_[p])
      * (borelElem p b₁ b₂ y : Matrix (Fin 2) (Fin 2) ℚ_[p]) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]


public theorem borelElem_inv (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    (borelElem p a₁ a₂ x)⁻¹
      = borelElem p a₁⁻¹ a₂⁻¹
          (-(((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * x * ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p]))) :=
  Units.ext rfl


@[simp] public theorem borelElem_one : borelElem p 1 1 0 = 1 := by
  apply Units.ext
  show (borelElem p 1 1 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end BorelElements

section HalfModulus


public theorem halfModulus_eq_one_of_norm_eq_one {a₁ a₂ : ℚ_[p]ˣ}
    (h₁ : ‖(a₁ : ℚ_[p])‖ = 1) (h₂ : ‖(a₂ : ℚ_[p])‖ = 1) : halfModulus p a₁ a₂ = 1 := by
  simp only [halfModulus, h₁, h₂, div_one, Real.sqrt_one, Complex.ofReal_one]


@[simp] public theorem halfModulus_one : halfModulus p 1 1 = 1 :=
  halfModulus_eq_one_of_norm_eq_one p (by simp) (by simp)


public theorem halfModulus_congr {a₁ a₂ b₁ b₂ : ℚ_[p]ˣ}
    (h₁ : ‖(a₁ : ℚ_[p])‖ = ‖(b₁ : ℚ_[p])‖) (h₂ : ‖(a₂ : ℚ_[p])‖ = ‖(b₂ : ℚ_[p])‖) :
    halfModulus p a₁ a₂ = halfModulus p b₁ b₂ := by
  simp only [halfModulus, h₁, h₂]


public theorem halfModulus_mul (a₁ a₂ b₁ b₂ : ℚ_[p]ˣ) :
    halfModulus p (a₁ * b₁) (a₂ * b₂) = halfModulus p a₁ a₂ * halfModulus p b₁ b₂ := by
  have hquot : ‖((a₁ * b₁ : ℚ_[p]ˣ) : ℚ_[p])‖ / ‖((a₂ * b₂ : ℚ_[p]ˣ) : ℚ_[p])‖
      = (‖(a₁ : ℚ_[p])‖ / ‖(a₂ : ℚ_[p])‖) * (‖(b₁ : ℚ_[p])‖ / ‖(b₂ : ℚ_[p])‖) := by
    rw [Units.val_mul, Units.val_mul, norm_mul, norm_mul, div_mul_div_comm]
  simp only [halfModulus, hquot]
  rw [Real.sqrt_mul (by positivity), Complex.ofReal_mul]

end HalfModulus

section PrincipalSeries


public theorem mem_principalSeries_iff {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {f : GL (Fin 2) ℚ_[p] → ℂ} :
    f ∈ principalSeries p μ₁ μ₂
      ↔ IsLocallyConstant f ∧
          ∀ (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (g : GL (Fin 2) ℚ_[p]),
            f (borelElem p a₁ a₂ x * g)
              = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ * f g :=
  Iff.rfl


public theorem isLocallyConstant_of_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂) : IsLocallyConstant f :=
  ((mem_principalSeries_iff p).mp hf).1


public theorem apply_borelElem_mul_of_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂)
    (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (g : GL (Fin 2) ℚ_[p]) :
    f (borelElem p a₁ a₂ x * g)
      = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ * f g :=
  ((mem_principalSeries_iff p).mp hf).2 a₁ a₂ x g


public theorem rightTranslate_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂) (g : GL (Fin 2) ℚ_[p]) :
    (fun y => f (y * g)) ∈ principalSeries p μ₁ μ₂ := by
  obtain ⟨hlc, htr⟩ := (mem_principalSeries_iff p).mp hf
  refine (mem_principalSeries_iff p).mpr
    ⟨hlc.comp_continuous (continuous_id.mul continuous_const), fun a₁ a₂ x g₀ => ?_⟩
  show f (borelElem p a₁ a₂ x * g₀ * g) = _ * f (g₀ * g)
  rw [mul_assoc, htr]

end PrincipalSeries

section RightInvariant


public theorem mem_rightInvariantFunctions_iff {U : Subgroup (GL (Fin 2) ℚ_[p])}
    {f : GL (Fin 2) ℚ_[p] → ℂ} :
    f ∈ rightInvariantFunctions p U ↔ ∀ u ∈ U, ∀ x, f (x * u) = f x :=
  Iff.rfl

end RightInvariant

section PrincipalSeriesCarrier

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)


public theorem toFn_mem (f : PSCarrier p μ₁ μ₂) : toFn p μ₁ μ₂ f ∈ principalSeries p μ₁ μ₂ :=
  (toSub p μ₁ μ₂ f).property


public theorem ext {f g : PSCarrier p μ₁ μ₂}
    (h : ∀ y, toFn p μ₁ μ₂ f y = toFn p μ₁ μ₂ g y) : f = g :=
  Subtype.ext (funext h)


@[simp] public theorem toFn_smul (g : GL (Fin 2) ℚ_[p]) (f : PSCarrier p μ₁ μ₂)
    (y : GL (Fin 2) ℚ_[p]) :
    toFn p μ₁ μ₂ (g • f) y = toFn p μ₁ μ₂ f (y * g) := rfl


@[simp] public theorem toFn_csmul (c : ℂ) (f : PSCarrier p μ₁ μ₂) (y : GL (Fin 2) ℚ_[p]) :
    toFn p μ₁ μ₂ (c • f) y = c * toFn p μ₁ μ₂ f y := rfl


public theorem finrank_fixed_eq (U : Subgroup (GL (Fin 2) ℚ_[p])) :
    Module.finrank ℂ ↥(LocalNewvector.fixedSubmodule U (PSCarrier p μ₁ μ₂))
      = Module.finrank ℂ ↥(principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p U) :=
  (fixedEquiv p μ₁ μ₂ U).finrank_eq

end PSCarrier

end PrincipalSeriesCarrier

end LocalNewvector

end
