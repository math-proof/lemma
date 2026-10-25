import Mathlib
import Def.AutomorphicForm_FormalBaseChange
import Lemma.AutomorphicForm.LocalLFactor
import Theorems.Thm_AutomorphicForm_isBaseChangeOf_formalBaseChange
import Structure.JPSS_CubicLiftFactor

set_option autoImplicit false

open IsDedekindDomain NumberField Polynomial

noncomputable section

namespace AutomorphicForm

variable {R : Type*} [CommRing R]

def gl3LFactorPoly (e1 e2 e3 : R) : Polynomial R :=
  1 - C e1 * X + C e2 * X ^ 2 - C e3 * X ^ 3

@[simp] theorem gl3LFactorPoly_def (e1 e2 e3 : R) :
    gl3LFactorPoly e1 e2 e3 = 1 - C e1 * X + C e2 * X ^ 2 - C e3 * X ^ 3 := rfl

@[simp] theorem coeff_zero_gl3LFactorPoly (e1 e2 e3 : R) :
    (gl3LFactorPoly e1 e2 e3).coeff 0 = 1 := by
  simp [gl3LFactorPoly, coeff_one, coeff_X_pow]

@[simp] theorem coeff_one_gl3LFactorPoly (e1 e2 e3 : R) :
    (gl3LFactorPoly e1 e2 e3).coeff 1 = -e1 := by
  simp [gl3LFactorPoly, coeff_one, coeff_C_mul, coeff_X_pow]

@[simp] theorem coeff_two_gl3LFactorPoly (e1 e2 e3 : R) :
    (gl3LFactorPoly e1 e2 e3).coeff 2 = e2 := by
  simp [gl3LFactorPoly, coeff_one, coeff_C_mul, coeff_X_pow]

@[simp] theorem coeff_three_gl3LFactorPoly (e1 e2 e3 : R) :
    (gl3LFactorPoly e1 e2 e3).coeff 3 = -e3 := by
  simp [gl3LFactorPoly, coeff_one, coeff_C_mul, coeff_X_pow]

theorem gl3LFactorPoly_inj {e1 e2 e3 e1' e2' e3' : R}
    (h : gl3LFactorPoly e1 e2 e3 = gl3LFactorPoly e1' e2' e3') :
    e1 = e1' ∧ e2 = e2' ∧ e3 = e3' := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (·.coeff 1) h
    simp only [coeff_one_gl3LFactorPoly] at this; exact neg_injective this
  · have := congrArg (·.coeff 2) h
    simpa only [coeff_two_gl3LFactorPoly] using this
  · have := congrArg (·.coeff 3) h
    simp only [coeff_three_gl3LFactorPoly] at this; exact neg_injective this

theorem gl3LFactorPoly_split (γ₁ γ₂ γ₃ : R) :
    gl3LFactorPoly (γ₁ + γ₂ + γ₃) (γ₁ * γ₂ + γ₁ * γ₃ + γ₂ * γ₃) (γ₁ * γ₂ * γ₃) =
      (1 - C γ₁ * X) * (1 - C γ₂ * X) * (1 - C γ₃ * X) := by
  simp only [gl3LFactorPoly, map_add, map_mul]; ring

theorem gl3LFactorPoly_inertInduction (c : R) :
    gl3LFactorPoly 0 0 c = 1 - C c * X ^ 3 := by
  simp [gl3LFactorPoly]

theorem gl3LFactorPoly_splitInduction (c₁ c₂ c₃ : R) :
    gl3LFactorPoly (c₁ + c₂ + c₃) (c₁ * c₂ + c₁ * c₃ + c₂ * c₃) (c₁ * c₂ * c₃) =
      (1 - C c₁ * X) * (1 - C c₂ * X) * (1 - C c₃ * X) :=
  gl3LFactorPoly_split c₁ c₂ c₃

theorem eulerCompare_inert (α β : R) :
    (heckeLFactorPoly (satakePow 3 (α + β) (α * β)) ((α * β) ^ 3)).comp (X ^ 3) =
      (1 - C (α ^ 3) * X ^ 3) * (1 - C (β ^ 3) * X ^ 3) := by
  rw [satakePow_add_pow, mul_pow, heckeLFactorPoly_split]
  simp only [mul_comp, sub_comp, one_comp, C_comp, X_comp]

theorem eulerCompare_inert_symm (s e : R) :
    (heckeLFactorPoly (satakePow 3 s e) (e ^ 3)).comp (X ^ 3) =
      1 - C (satakePow 3 s e) * X ^ 3 + C (e ^ 3) * X ^ 6 := by
  simp only [heckeLFactorPoly_def, sub_comp, add_comp, one_comp, mul_comp, C_comp,
    X_comp, pow_comp]
  ring

theorem rankinFactor_inert (α β c : R) :
    (1 - C (c * α ^ 3) * X ^ 3) * (1 - C (c * β ^ 3) * X ^ 3) =
      1 - C (c * (α ^ 3 + β ^ 3)) * X ^ 3 + C (c ^ 2 * (α * β) ^ 3) * X ^ 6 := by
  push_cast [map_mul, map_add, map_pow]; ring

theorem eulerCompare_inert_twist (s e c : R) :
    (heckeLFactorPoly (c * satakePow 3 s e) (c ^ 2 * e ^ 3)).comp (X ^ 3) =
      1 - C (c * satakePow 3 s e) * X ^ 3 + C (c ^ 2 * e ^ 3) * X ^ 6 := by
  simp only [heckeLFactorPoly_def, sub_comp, add_comp, one_comp, mul_comp, C_comp,
    X_comp, pow_comp]
  ring

section Factor

variable (R : Type*) [CommRing R]
  (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]


variable {R F K}

def JPSSConverseFactored.toJPSSCubicLiftPackage (I : JPSSConverseFactored R F K) :
    JPSSCubicLiftPackage R F K where
  notion := I.notion
  cubicDeg := I.cubicDeg
  lift_automorphic := fun π hπ =>
    ⟨formalBaseChange F K π, isBaseChangeOf_formalBaseChange F K π,
      I.jl_converse _ (I.formalLift_converseHyp π hπ)⟩

variable (R F K)


variable {R F K}

def JPSSGL3Factored.toJPSSCubicLiftPackage (I : JPSSGL3Factored R F K) :
    JPSSCubicLiftPackage R F K :=
  I.toJPSSConverseFactored.toJPSSCubicLiftPackage

theorem JPSSGL3Factored.converseHyp_of_ingredients (I : JPSSGL3Factored R F K)
    (π : HeckeEigensystem F R) (hπ : I.notion.IsCusp F π) :
    I.ConverseHyp (formalBaseChange F K π) :=
  I.euler_compare π fun χ hirr =>
    let ⟨σ, hσ⟩ := I.gl3_induction χ hirr; ⟨σ, hσ, I.rankin_nice π hπ σ hσ⟩

end Factor

def trivialNotion (R : Type*) [CommRing R] : CuspidalityNotion R where
  IsCusp := fun _ _ _ _ => True

section SAT

variable (R : Type*) [CommRing R]
  (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

def jpssConverseFactored_sat
    (hcubic : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), IsDegreeThreeOutside F K S) :
    JPSSConverseFactored R F K where
  notion := trivialNotion R
  cubicDeg := hcubic
  ConverseHyp := fun _ => True
  jl_converse := fun _ _ => Or.inl trivial
  formalLift_converseHyp := fun _ _ => trivial

def jpssGL3Factored_sat
    (hcubic : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), IsDegreeThreeOutside F K S) :
    JPSSGL3Factored R F K where
  notion := trivialNotion R
  cubicDeg := hcubic
  ConverseHyp := fun _ => True
  jl_converse := fun _ _ => Or.inl trivial
  formalLift_converseHyp := fun _ _ => trivial
  IsGL3Automorphic := fun _ => True
  RankinNice := fun _ _ => True
  IsIrreducibleInduced := fun _ => True
  gl3_induction := fun _ _ => ⟨fun _ => (0, 0, 0), trivial⟩
  rankin_nice := fun _ _ _ _ => trivial
  euler_compare := fun _ _ => trivial
  formalLift_converseHyp_eq := fun _ _ => rfl

theorem jpssGL3Factored_sat_toPackage_notion
    (hcubic : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), IsDegreeThreeOutside F K S) :
    ((jpssGL3Factored_sat R F K hcubic).toJPSSCubicLiftPackage).notion = trivialNotion R :=
  rfl

def jpssConverseFactored_sat_toPackage
    (hcubic : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), IsDegreeThreeOutside F K S) :
    JPSSCubicLiftPackage R F K :=
  (jpssConverseFactored_sat R F K hcubic).toJPSSCubicLiftPackage

end SAT

end AutomorphicForm

end
