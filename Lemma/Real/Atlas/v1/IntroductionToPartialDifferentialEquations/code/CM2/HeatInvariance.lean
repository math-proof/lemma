import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM2.HeatInvariance
open Finset HeatEquationInvariance


namespace HeatEquationInvariance

/--
[deriv_const_mul_fn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM2/HeatInvariance.lean)
-/
@[path]
lemma deriv_const_mul_fn
  {A : ℝ}
  {f : ℝ → ℝ}
  {t : ℝ} :
-- imply
  deriv (fun s => A * f s) t = A * deriv f t :=
-- proof
  deriv_const_mul_field A

end HeatEquationInvariance

namespace HeatEquationInvariance

/--
[laplacian_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM2/HeatInvariance.lean)
-/
@[path]
lemma laplacian_const_mul
  {n : ℕ}
  {A : ℝ}
  {f : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ} :
-- imply
  laplacian (fun y => A * f y) x = A * laplacian f x := by
-- proof
  unfold laplacian
  simp_rw [deriv_const_mul_field A]
  rw [← Finset.mul_sum]

end HeatEquationInvariance

namespace HeatEquationInvariance

/--
[deriv_time_translate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM2/HeatInvariance.lean)
-/
@[path]
lemma deriv_time_translate
  {n : ℕ}
  {u : ℝ → (Fin n → ℝ) → ℝ}
  {t₀ t : ℝ}
  {x : Fin n → ℝ} :
-- imply
  deriv (fun s => u (s - t₀) x) t = deriv (fun s => u s x) (t - t₀) :=
-- proof
  deriv_comp_sub_const (fun s => u s x) t₀ t

end HeatEquationInvariance

namespace HeatEquationInvariance

/--
[laplacian_translate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM2/HeatInvariance.lean)
-/
@[path]
lemma laplacian_translate
  {n : ℕ}
  {f : (Fin n → ℝ) → ℝ}
  {x₀ x : Fin n → ℝ} :
-- imply
  laplacian (fun y => f (y - x₀)) x = laplacian f (x - x₀) := by
-- proof
  unfold laplacian
  congr 1
  ext i
  have key : ∀ xi, Function.update x i xi - x₀ = Function.update (x - x₀) i (xi - x₀ i) := by
    intro xi
    ext j
    simp [Function.update, Pi.sub_apply]
    split <;> simp_all
  simp_rw [key]
  have key2 : ∀ h, deriv (fun xi => f (Function.update (x - x₀) i (xi - x₀ i))) (x i + h)
    = deriv (fun xi => f (Function.update (x - x₀) i xi)) (x i + h - x₀ i) := by
    intro h
    exact deriv_comp_sub_const (fun xi => f (Function.update (x - x₀) i xi)) (x₀ i) (x i + h)
  simp_rw [key2]
  congr 1
  ext h
  congr 1
  simp [Pi.sub_apply]
  ring

end HeatEquationInvariance

namespace HeatEquationInvariance

/--
[deriv_time_dilate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM2/HeatInvariance.lean)
-/
@[path]
lemma deriv_time_dilate
  {n : ℕ}
  {u : ℝ → (Fin n → ℝ) → ℝ}
  {lam t : ℝ}
  {x : Fin n → ℝ} :
-- imply
  deriv (fun s => u (lam ^ 2 * s) x) t = lam ^ 2 * deriv (fun s => u s x) (lam ^ 2 * t) := by
-- proof
  have := deriv_comp_mul_left (lam ^ 2) (fun s => u s x) t
  simp [smul_eq_mul] at this
  exact this

end HeatEquationInvariance

namespace HeatEquationInvariance

/--
[laplacian_dilate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM2/HeatInvariance.lean)
-/
@[path]
lemma laplacian_dilate
  {n : ℕ}
  {f : (Fin n → ℝ) → ℝ}
  {lam : ℝ}
  {x : Fin n → ℝ} :
-- imply
  laplacian (fun y => f (lam • y)) x = lam ^ 2 * laplacian f (lam • x) := by
-- proof
  unfold laplacian
  rw [Finset.mul_sum]
  congr 1
  ext i
  have smul_update : ∀ xi, lam • Function.update x i xi = Function.update (lam • x) i (lam * xi) := by
    intro xi; ext j; simp [Function.update, Pi.smul_apply, smul_eq_mul]
  simp_rw [smul_update]
  have inner : ∀ h,
    deriv (fun xi => f (Function.update (lam • x) i (lam * xi))) (x i + h) =
    lam * deriv (fun xi => f (Function.update (lam • x) i xi)) (lam * (x i + h)) := by
    intro h
    have := @deriv_comp_mul_left ℝ ℝ _ _ _ lam (fun xi => f (Function.update (lam • x) i xi)) (x i + h)
    simp [smul_eq_mul] at this; exact this
  simp_rw [inner]
  have shift : ∀ h, lam * (x i + h) = (lam • x) i + lam * h := by
    intro h; simp [Pi.smul_apply, smul_eq_mul, mul_add]
  simp_rw [shift]
  set g := fun xi => f (Function.update (lam • x) i xi)
  set G := fun h => deriv g ((lam • x) i + h)
  conv_lhs =>
    arg 1; ext h
    rw [show lam * G (lam * h) = lam * (G ∘ (lam * ·)) h from by simp [Function.comp]]
  rw [deriv_const_mul_field lam]
  have comp_unfold : G ∘ (lam * ·) = fun h => G (lam * h) := by ext; simp [Function.comp]
  rw [comp_unfold]
  have outer := @deriv_comp_mul_left ℝ ℝ _ _ _ lam G 0
  simp [smul_eq_mul] at outer
  rw [outer]
  ring

end HeatEquationInvariance

namespace HeatEquationInvariance

/--
[heat_translation_invariance](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM2/HeatInvariance.lean)
-/
@[path]
lemma heat_translation_invariance
  {n : ℕ}
  {D : ℝ}
  {u : ℝ → (Fin n → ℝ) → ℝ}
  {A t₀ : ℝ}
  {x₀ : Fin n → ℝ}
-- given
  (_hD : D > 0)
  (hu : ∀ t x, heatOperator D u t x = 0) :
-- imply
  ∀ t x, heatOperator D (fun t x => A * u (t - t₀) (x - x₀)) t x = 0 := by
-- proof
  intro t x
  unfold heatOperator
  rw [deriv_const_mul_fn A (fun s => u (s - t₀) (x - x₀)) t]
  rw [deriv_time_translate u t₀ t (x - x₀)]
  rw [laplacian_const_mul A (fun y => u (t - t₀) (y - x₀)) x]
  rw [laplacian_translate (u (t - t₀)) x₀ x]
  have h := hu (t - t₀) (x - x₀)
  unfold heatOperator at h
  linear_combination A * h

end HeatEquationInvariance

namespace HeatEquationInvariance

/--
[heat_parabolic_dilation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM2/HeatInvariance.lean)
-/
@[path]
lemma heat_parabolic_dilation
  {n : ℕ}
  {D : ℝ}
  {u : ℝ → (Fin n → ℝ) → ℝ}
  {A lam : ℝ}
-- given
  (_hD : D > 0)
  (hu : ∀ t x, heatOperator D u t x = 0)
  (_hlam : lam > 0) :
-- imply
  ∀ t x, heatOperator D (fun t x => A * u (lam ^ 2 * t) (lam • x)) t x = 0 := by
-- proof
  intro t x
  unfold heatOperator
  rw [deriv_const_mul_fn A (fun s => u (lam ^ 2 * s) (lam • x)) t]
  rw [deriv_time_dilate u lam t (lam • x)]
  rw [laplacian_const_mul A (fun y => u (lam ^ 2 * t) (lam • y)) x]
  rw [laplacian_dilate (u (lam ^ 2 * t)) lam x]
  have h := hu (lam ^ 2 * t) (lam • x)
  unfold heatOperator at h
  linear_combination A * lam ^ 2 * h

end HeatEquationInvariance

namespace HeatEquationInvariance

/--
[heat_equation_invariance](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM2/HeatInvariance.lean)
-/
@[path]
lemma heat_equation_invariance
  {n : ℕ}
  {D : ℝ}
  {u : ℝ → (Fin n → ℝ) → ℝ}
-- given
  (hD : D > 0)
  (hu : ∀ t x, heatOperator D u t x = 0) :
-- imply
  (∀ (A t₀ : ℝ) (x₀ : Fin n → ℝ), ∀ t x, heatOperator D (fun t x => A * u (t - t₀) (x - x₀)) t x = 0) ∧ (∀ (A lam : ℝ) (_hlam : lam > 0), ∀ t x, heatOperator D (fun t x => A * u (lam ^ 2 * t) (lam • x)) t x = 0) :=
-- proof
  ⟨fun A t₀ x₀ => heat_translation_invariance hD u hu A t₀ x₀,
    fun A lam hlam => heat_parabolic_dilation hD u hu A lam hlam⟩
end HeatEquationInvariance



-- created on 2026-10-23
