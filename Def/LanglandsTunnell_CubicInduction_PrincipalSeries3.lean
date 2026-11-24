module
public import Def.LanglandsTunnell_CubicInduction_Structure
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
set_option autoImplicit false
open Matrix IsDedekindDomain NumberField Matrix.AdelicLevel LanglandsTunnell.TateLocal


public section

noncomputable section

namespace LanglandsTunnell.CubicInduction

section PrincipalSeries3

variable (v : HeightOneSpectrum (𝓞 ℚ))

def diagonal3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : LocalGL3 v where
  val := diagonal fun i => (a i : v.adicCompletion ℚ)
  inv := diagonal fun i => ((a i)⁻¹ : (v.adicCompletion ℚ)ˣ)
  val_inv := by
    rw [diagonal_mul_diagonal]
    simp only [Units.mul_inv, diagonal_one]
  inv_val := by
    rw [diagonal_mul_diagonal]
    simp only [Units.inv_mul, diagonal_one]

def halfModulus3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : ℂ :=
  ((‖(a 0 : v.adicCompletion ℚ)‖ / ‖(a 2 : v.adicCompletion ℚ)‖ : ℝ) : ℂ)

def torusChar3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : ℂ :=
  ∏ i : Fin 3, ((χ i (a i) : ℂˣ) : ℂ)

def principalSeries3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : Submodule ℂ (LocalGL3 v → ℂ) where
  carrier := {f | IsLocallyConstant f ∧
    (∀ (x y z : v.adicCompletion ℚ) (g : LocalGL3 v), f (upperUnipotent3 x y z * g) = f g) ∧
    ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v),
      f (diagonal3 v a * g) = torusChar3 v χ a * halfModulus3 v a * f g}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ _ _ _ => rfl, fun _ _ => by simp⟩
  add_mem' := by
    intro f₁ f₂ h₁ h₂
    obtain ⟨h₁lc, h₁n, h₁t⟩ := h₁
    obtain ⟨h₂lc, h₂n, h₂t⟩ := h₂
    refine ⟨h₁lc.comp₂ h₂lc (· + ·), fun x y z g => ?_, fun a g => ?_⟩
    · show f₁ _ + f₂ _ = f₁ g + f₂ g
      rw [h₁n, h₂n]
    · show f₁ _ + f₂ _ = _ * (f₁ g + f₂ g)
      rw [h₁t, h₂t]
      ring
  smul_mem' := by
    intro c f hf
    obtain ⟨hlc, hn, ht⟩ := hf
    refine ⟨hlc.comp (c * ·), fun x y z g => ?_, fun a g => ?_⟩
    · show c * f _ = c * f g
      rw [hn]
    · show c * f _ = _ * (c * f g)
      rw [ht]
      ring

variable {v}

def coefficientFn {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} (L : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)
    (f : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ :=
  fun g => L ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩

def IsWhittakerFunctional3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ (x y z : v.adicCompletion ℚ) (F : ↥(principalSeries3 v χ)),
    Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) F,
        rightTranslate_mem_principalSeries3 F.2 (upperUnipotent3 x y z)⟩ = ψ (x + y) * Λ F

end PrincipalSeries3

section Witness

variable (v : HeightOneSpectrum (𝓞 ℚ))

def gl3Entry (g : LocalGL3 v) (i j : Fin 3) : v.adicCompletion ℚ :=
  (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j

def cornerEntry (g : LocalGL3 v) : v.adicCompletion ℚ := gl3Entry v g 2 0

def lowerMinor (g : LocalGL3 v) : v.adicCompletion ℚ :=
  gl3Entry v g 1 0 * gl3Entry v g 2 1 - gl3Entry v g 1 1 * gl3Entry v g 2 0

def outerMinor (g : LocalGL3 v) : v.adicCompletion ℚ :=
  gl3Entry v g 1 0 * gl3Entry v g 2 2 - gl3Entry v g 1 2 * gl3Entry v g 2 0

def gl3Det (g : LocalGL3 v) : v.adicCompletion ℚ := (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det

def cellRatio (g : LocalGL3 v) : Fin 3 → v.adicCompletion ℚ :=
  ![gl3Entry v g 2 1 / cornerEntry v g, gl3Entry v g 2 2 / cornerEntry v g, outerMinor v g / lowerMinor v g]

def cellCutoff : Set (LocalGL3 v) :=
  {g | cornerEntry v g ≠ 0 ∧ lowerMinor v g ≠ 0 ∧ ∀ i, Valued.v (cellRatio v g i) ≤ 1}

def cellValue (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL3 v) : ℂ :=
  charExt (χ 0) (gl3Det v g / lowerMinor v g) * charExt (χ 1) (lowerMinor v g / cornerEntry v g) *
    charExt (χ 2) (cornerEntry v g) *
    ((‖gl3Det v g / lowerMinor v g‖ / ‖cornerEntry v g‖ : ℝ) : ℂ)

def cellSection (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : LocalGL3 v → ℂ :=
  (cellCutoff v).indicator (cellValue v χ)

def antidiagonal3 : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : v.adicCompletion ℚ), 0, 1; 0, 1, 0; 1, 0, 0] (by
    simp [Matrix.det_fin_three])

end Witness

section WitnessTopology

open Filter Topology

variable (v : HeightOneSpectrum (𝓞 ℚ))

def cellVector (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i)) :
    ↥(principalSeries3 v χ) :=
  ⟨cellSection v χ, cellSection_mem_principalSeries3 v χ hχ⟩

def evalAntidiagonal3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ :=
  (LinearMap.proj (antidiagonal3 v) : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ).comp (principalSeries3 v χ).subtype

end WitnessTopology

end LanglandsTunnell.CubicInduction

end
