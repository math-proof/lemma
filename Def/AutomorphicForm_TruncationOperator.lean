import Def.AutomorphicForm_ConstantTerm

set_option autoImplicit false

open MeasureTheory

namespace AutomorphicForm

section GrowthDecay

variable {G : Type*}

def IsSlowlyIncreasingOn (S : Set G) (H : G → ℝ) (φ : G → ℂ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ g ∈ S, ‖φ g‖ ≤ C * H g ^ N

def IsRapidlyDecreasingOn (S : Set G) (H : G → ℝ) (φ : G → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ g ∈ S, ‖φ g‖ ≤ C * (H g)⁻¹ ^ N


def highSet (H : G → ℝ) (T : ℝ) : Set G :=
  {g : G | T < H g}

end GrowthDecay

section LambdaT

variable {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]

noncomputable def lambdaT (μ : Measure Q) (u : Q → G) (H : G → ℝ) (T : ℝ) (φ : G → ℂ) :
    G → ℂ :=
  fun g => φ g - Set.indicator (highSet H T) (constantTerm μ u φ) g

end LambdaT

end AutomorphicForm
