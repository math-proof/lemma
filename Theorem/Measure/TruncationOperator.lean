module

public import Def.AutomorphicForm_ConstantTerm
public import Def.AutomorphicForm_TruncationOperator

public section

set_option autoImplicit false

open MeasureTheory

namespace AutomorphicForm

section GrowthDecay

variable {G : Type*}


public theorem isSlowlyIncreasingOn_of_bounded {S : Set G} {H : G → ℝ} {φ : G → ℂ} {C : ℝ}
    (hC : ∀ g ∈ S, ‖φ g‖ ≤ C) : IsSlowlyIncreasingOn S H φ :=
  ⟨C, 0, fun g hg => by simpa using hC g hg⟩

public theorem isSlowlyIncreasingOn_const_one (S : Set G) (H : G → ℝ) :
    IsSlowlyIncreasingOn S H (fun _ => (1 : ℂ)) :=
  isSlowlyIncreasingOn_of_bounded (C := 1) (fun _ _ => by simp)

public theorem isRapidlyDecreasingOn_zero (S : Set G) (H : G → ℝ) :
    IsRapidlyDecreasingOn S H (fun _ => (0 : ℂ)) :=
  fun _ => ⟨0, fun _ _ => by simp⟩

public theorem IsRapidlyDecreasingOn.isSlowlyIncreasingOn {S : Set G} {H : G → ℝ} {φ : G → ℂ}
    (h : IsRapidlyDecreasingOn S H φ) : IsSlowlyIncreasingOn S H φ := by
  obtain ⟨C, hC⟩ := h 0
  exact ⟨C, 0, fun g hg => by simpa using hC g hg⟩


public theorem mem_highSet_iff {H : G → ℝ} {T : ℝ} {g : G} : g ∈ highSet H T ↔ T < H g :=
  Iff.rfl

end GrowthDecay

section LambdaT

variable {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]


public theorem lambdaT_apply (μ : Measure Q) (u : Q → G) (H : G → ℝ) (T : ℝ) (φ : G → ℂ) (g : G) :
    lambdaT μ u H T φ g = φ g - Set.indicator (highSet H T) (constantTerm μ u φ) g :=
  rfl

public theorem lambdaT_apply_of_le (μ : Measure Q) (u : Q → G) {H : G → ℝ} {T : ℝ} {g : G}
    (hg : H g ≤ T) (φ : G → ℂ) : lambdaT μ u H T φ g = φ g := by
  unfold lambdaT
  rw [Set.indicator_of_notMem (by simpa [mem_highSet_iff, not_lt] using hg), sub_zero]

public theorem lambdaT_apply_of_lt (μ : Measure Q) (u : Q → G) {H : G → ℝ} {T : ℝ} {g : G}
    (hg : T < H g) (φ : G → ℂ) : lambdaT μ u H T φ g = φ g - constantTerm μ u φ g := by
  unfold lambdaT
  rw [Set.indicator_of_mem (mem_highSet_iff.mpr hg)]

public theorem lambdaT_zero (μ : Measure Q) (u : Q → G) (H : G → ℝ) (T : ℝ) :
    lambdaT μ u H T (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  funext g
  simp [lambdaT]

public theorem lambdaT_of_isCuspidalFn (μ : Measure Q) (u : Q → G) {φ : G → ℂ}
    (hφ : IsCuspidalFn μ u φ) (H : G → ℝ) (T : ℝ) : lambdaT μ u H T φ = φ := by
  funext g
  unfold lambdaT
  by_cases hmem : g ∈ highSet H T
  · rw [Set.indicator_of_mem hmem, hφ g, sub_zero]
  · rw [Set.indicator_of_notMem hmem, sub_zero]

end LambdaT

end AutomorphicForm
