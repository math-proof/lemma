import Mathlib

set_option autoImplicit false

open Filter Ideal NumberField NumberField.InfinitePlace NumberField.Units Topology
  nonZeroDivisors

open scoped Real

namespace FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

def classZetaCoeff (C : ClassGroup (𝓞 K)) (n : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n ∧ ClassGroup.mk0 I = C}

def classZeta (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ classZetaCoeff K C n) s

def classResidue : ℝ :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K) /
    (torsionOrder K * Real.sqrt |discr K|)

def classGroupLSeries (χ : ClassGroup (𝓞 K) →* ℂ) (s : ℂ) : ℂ :=
  ∑ C : ClassGroup (𝓞 K), χ C * classZeta K C s

def LSeriesInheritsPole (χ : ClassGroup (𝓞 K) →* ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ s : ℝ in 𝓝[>] 1, c ≤ ‖(fun s : ℝ ↦ (s - 1) * classGroupLSeries K χ s) s‖

end

end FrobeniusDensity
