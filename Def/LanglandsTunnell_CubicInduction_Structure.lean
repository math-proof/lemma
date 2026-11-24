module
public import Def.LanglandsTunnell_CubicInduction_Carrier
public import Def.LanglandsTunnell_CubicInduction_HeckeDatum
public import Theorem.Matrix.CubicInduction_Growth
public import Def.LanglandsTunnell_CubicInduction_IotaTorus
public import Theorem.Matrix.CubicInduction_Congruence
public import Theorem.Matrix.CubicInduction_TorusValues
public import Theorem.Measure.WhittakerCoefficient
public import Theorem.Measure.TateGlobalZeta
public import Def.AutomorphicForm_SmoothingKernel
public import Structure.LanglandsTunnell_CubicInduction_Structure
set_option autoImplicit false
open Matrix IsDedekindDomain NumberField MeasureTheory Measure


public section

noncomputable section

namespace LanglandsTunnell.CubicInduction

export AutomorphicForm (transposeInvN coe_transposeInvN)

universe u v w

section LocalWhittaker

variable {F : Type u} [CommRing F] {R : Type v} [CommRing R]


def gl3PsiWhittakerFnSpace (F : Type u) [CommRing F] (R : Type v) [CommRing R]
    (ψ : AddChar F R) : Submodule R (GL (Fin 3) F → R) where
  carrier := {W | IsGL3PsiWhittakerFn ψ W}
  add_mem' := by
    intro W₁ W₂ h₁ h₂ x y z g
    simp only [Pi.add_apply, h₁ x y z g, h₂ x y z g]
    ring
  zero_mem' := by
    intro x y z g
    simp only [Pi.zero_apply, mul_zero]
  smul_mem' := by
    intro c W hW x y z g
    simp only [Pi.smul_apply, hW x y z g, smul_eq_mul]
    ring

variable {V : Type w} [AddCommGroup V] [Module R V]


end LocalWhittaker


section Global

open AutomorphicForm Measure Matrix

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]


open scoped Classical in


attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel


def HasCubicInductionForm (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop :=
  ∃ D : CubicInductionForm K pins ψ μ,
    D.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        D.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (D.whittakerLoc v)

def CubicInductionForm.zero (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : CubicInductionForm K pins ψ μ where
  form := 0
  whittaker := 0
  whittakerLoc := fun _ _ => 0
  whittakerArch := 0
  centralChar := 1
  dualWhittaker := 0
  automorphic := fun _ _ => rfl
  central := fun _ _ => by simp
  centralChar_ideleClass := fun _ => rfl
  cuspidalP21 := fun _ => by simp
  cuspidalP12 := fun _ => by simp
  whittaker_eq := fun _ => by simp only [whittaker3, Pi.zero_apply, zero_mul, MeasureTheory.integral_zero]
  whittaker_law := fun _ _ _ _ => (mul_zero _).symm
  expansion := fun _ => by simpa only [Pi.zero_apply] using hasSum_zero
  whittakerLoc_law := fun _ _ _ _ _ => (mul_zero _).symm
  factorizable := fun _ _ _ _ => by simp
  spherical := fun v _ => isInducedSphericalAt_zero _ v _
  levelInvariant := fun _ _ _ _ _ => rfl
  multOne := fun v => hasWhittakerMultOne_zero (psiLoc ψ v)
  moderateGrowth := isModerateGrowth3_zero ℚ
  kFinite := ⟨∅, fun _ _ => by
    simp only [Finset.coe_empty, Submodule.span_empty]
    exact Submodule.zero_mem _⟩
  iotaMoments := fun _ _ _ => by
    simp only [Pi.zero_apply, nnnorm_zero, ENNReal.coe_zero, zero_mul, MeasureTheory.lintegral_zero,
      ENNReal.zero_lt_top]
  whittakerHalfPlane := ⟨0, fun _ _ _ _ => by
    simp only [tsum_zero, Pi.zero_apply, nnnorm_zero, ENNReal.coe_zero, zero_mul, MeasureTheory.lintegral_zero,
      ENNReal.zero_lt_top]⟩
  dualWhittaker_eq := fun _ => by
    simp only [whittaker3, dualForm, Pi.zero_apply, zero_mul, MeasureTheory.integral_zero]
  dualWhittaker_law := fun _ _ _ _ => (mul_zero _).symm
  dual_expansion := fun _ => by simpa only [dualForm, Pi.zero_apply] using hasSum_zero
  dual_iotaMoments := fun _ _ _ => by
    simp only [dualForm, Pi.zero_apply, nnnorm_zero, ENNReal.coe_zero, zero_mul, MeasureTheory.lintegral_zero,
      ENNReal.zero_lt_top]
  dual_whittakerHalfPlane := ⟨0, fun _ _ _ _ => by
    simp only [tsum_zero, Pi.zero_apply, nnnorm_zero, ENNReal.coe_zero, zero_mul, MeasureTheory.lintegral_zero,
      ENNReal.zero_lt_top]⟩

end Global

end LanglandsTunnell.CubicInduction

end
