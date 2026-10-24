import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix
open LanglandsTunnell.RankinSelberg

noncomputable section

namespace LanglandsTunnell.CubicInduction

def sphericalTorusValue (e₁ e₂ e₃ : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => e₁
  | 2 => e₁ ^ 2 - e₂
  | n + 3 =>
    e₁ * sphericalTorusValue e₁ e₂ e₃ (n + 2) - e₂ * sphericalTorusValue e₁ e₂ e₃ (n + 1) +
      e₃ * sphericalTorusValue e₁ e₂ e₃ n

section TwoRowPoint

variable {A : Type*} [CommRing A]

def diagUnits2 (x y : Aˣ) : GL (Fin 2) A where
  val := !![(x : A), 0; 0, (y : A)]
  inv := !![((x⁻¹ : Aˣ) : A), 0; 0, ((y⁻¹ : Aˣ) : A)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem coe_diagUnits2 (x y : Aˣ) :
    ((diagUnits2 x y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(x : A), 0; 0, (y : A)] :=
  rfl

theorem diagUnits2_one_right (x : Aˣ) : diagUnits2 x 1 = diagUnitGL2 x := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagUnits2, diagUnitGL2]

variable (v : HeightOneSpectrum (𝓞 ℚ))

def twoRowPointLocal (k₁ k₂ : ℕ) : GL (Fin 3) (v.adicCompletion ℚ) :=
  iotaGL (diagUnits2 (ratPrimeUnit v ^ k₁) (ratPrimeUnit v ^ k₂))

theorem twoRowPointLocal_zero_right (k : ℕ) : twoRowPointLocal v k 0 = iotaTorusLocal v k := by
  simp only [twoRowPointLocal, iotaTorusLocal, pow_zero, diagUnits2_one_right, diagHom_apply]

end TwoRowPoint

section Clause

variable {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

def HasSphericalTorusValuesAt (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 v → ℂ) : Prop :=
  (∀ n : ℕ, W (iotaTorusLocal v n) =
    (cNormQ v)⁻¹ ^ n * sphericalTorusValue (inducedE1 ℚ c v) (inducedE2 ℚ c v) (inducedE3 ℚ c v) n) ∧
  (∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) =
    (cNormQ v)⁻¹ ^ k₁ *
      (sphericalTorusValue (inducedE1 ℚ c v) (inducedE2 ℚ c v) (inducedE3 ℚ c v) k₁ *
          sphericalTorusValue (inducedE1 ℚ c v) (inducedE2 ℚ c v) (inducedE3 ℚ c v) (k₂ + 1) -
        sphericalTorusValue (inducedE1 ℚ c v) (inducedE2 ℚ c v) (inducedE3 ℚ c v) (k₁ + 1) *
          sphericalTorusValue (inducedE1 ℚ c v) (inducedE2 ℚ c v) (inducedE3 ℚ c v) k₂))

theorem not_hasSphericalTorusValuesAt_zero (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) : ¬ HasSphericalTorusValuesAt c v (fun _ => (0 : ℂ)) := by
  intro h
  have h0 := h.1 0
  simp [sphericalTorusValue] at h0

end Clause

end LanglandsTunnell.CubicInduction

end
