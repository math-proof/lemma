import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

noncomputable section

namespace HalfLine

def slope (F : ℝ → ℂ) : ℂ :=
  Filter.limUnder Filter.atTop (fun R : ℝ => F (R + 1) - F R)

def intercept (F : ℝ → ℂ) : ℂ :=
  Filter.limUnder Filter.atTop (fun R : ℝ => F R - (R : ℂ) * slope F)

theorem slope_eq_of_forall_le_eq_add_mul {F : ℝ → ℂ} {μ ν : ℂ}
    (h : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → F R = (R : ℂ) * ν + μ) : slope F = ν := by
  obtain ⟨R₀, hR⟩ := h
  unfold slope
  refine Filter.Tendsto.limUnder_eq ?_
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [Filter.eventually_ge_atTop R₀] with R hRle
  rw [hR (R + 1) (by linarith), hR R hRle]
  push_cast
  ring

theorem intercept_eq_of_forall_le_eq_add_mul {F : ℝ → ℂ} {μ ν : ℂ}
    (h : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → F R = (R : ℂ) * ν + μ) : intercept F = μ := by
  have hs : slope F = ν := slope_eq_of_forall_le_eq_add_mul h
  obtain ⟨R₀, hR⟩ := h
  unfold intercept
  refine Filter.Tendsto.limUnder_eq ?_
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [Filter.eventually_ge_atTop R₀] with R hRle
  rw [hs, hR R hRle]
  ring

theorem eq_and_eq_of_forall_le_eq_add_mul {F : ℝ → ℂ} {μ ν μ' ν' : ℂ}
    (h : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → F R = (R : ℂ) * ν + μ)
    (h' : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → F R = (R : ℂ) * ν' + μ') : μ = μ' ∧ ν = ν' :=
  ⟨(intercept_eq_of_forall_le_eq_add_mul h).symm.trans (intercept_eq_of_forall_le_eq_add_mul h'),
    (slope_eq_of_forall_le_eq_add_mul h).symm.trans (slope_eq_of_forall_le_eq_add_mul h')⟩

def affineExample (R : ℝ) : ℂ :=
  if R < 5 then 37 else (R : ℂ) * 3 + 7

theorem affineExample_eq (R : ℝ) (hR : 5 ≤ R) : affineExample R = (R : ℂ) * 3 + 7 := by
  simp [affineExample, not_lt.mpr hR]

theorem slope_affineExample : slope affineExample = 3 :=
  slope_eq_of_forall_le_eq_add_mul ⟨5, affineExample_eq⟩

theorem intercept_affineExample : intercept affineExample = 7 :=
  intercept_eq_of_forall_le_eq_add_mul ⟨5, affineExample_eq⟩

theorem affineExample_zero : affineExample 0 = 37 := by
  norm_num [affineExample]

example : intercept (fun x : ℝ => (7 : ℂ) + 3 * (x : ℂ)) = 7 :=
  intercept_eq_of_forall_le_eq_add_mul ⟨0, fun R _ => show (7 : ℂ) + 3 * (R : ℂ) = (R : ℂ) * 3 + 7 by ring⟩

example : slope (fun x : ℝ => (7 : ℂ) + 3 * (x : ℂ)) = 3 :=
  slope_eq_of_forall_le_eq_add_mul ⟨0, fun R _ => show (7 : ℂ) + 3 * (R : ℂ) = (R : ℂ) * 3 + 7 by ring⟩

example : intercept (fun _ : ℝ => (7 : ℂ)) = 7 :=
  intercept_eq_of_forall_le_eq_add_mul ⟨0, fun R _ => show (7 : ℂ) = (R : ℂ) * 0 + 7 by ring⟩

end HalfLine

end
