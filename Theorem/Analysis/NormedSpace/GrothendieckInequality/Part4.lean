/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.NormedSpace.GrothendieckInequality.Part4
open scoped InnerProductSpace


section

namespace FunctionalAnalysis.GrothendieckInequalityWanted

-- N10i
theorem scaledVec_inner {d : ℕ} (f g : (Fin d → Bool) → ℝ) :
    ⟪scaledVec f, scaledVec g⟫_ℝ = ((2:ℝ)^d)⁻¹ * ∑ ω, f ω * g ω := by
  have e : ⟪scaledVec f, scaledVec g⟫_ℝ
      = ∑ ω, (cubeScale d * f ω) * (cubeScale d * g ω) := by
    simp [scaledVec, PiLp.inner_apply, mul_comm]
  rw [e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  calc (cubeScale d * f ω) * (cubeScale d * g ω)
        = (cubeScale d * cubeScale d) * (f ω * g ω) := by ring
      _ = ((2:ℝ)^d)⁻¹ * (f ω * g ω) := by rw [cubeScale_sq]

-- N10ii
theorem scaledVec_norm_sq {d : ℕ} (f : (Fin d → Bool) → ℝ) :
    ‖scaledVec f‖^2 = ((2:ℝ)^d)⁻¹ * ∑ ω, f ω ^ 2 := by
  have e : ‖scaledVec f‖^2 = ∑ ω, (cubeScale d * f ω)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro ω _
    rfl
  rw [e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  calc (cubeScale d * f ω)^2
        = (cubeScale d * cubeScale d) * (f ω ^ 2) := by ring
      _ = ((2:ℝ)^d)⁻¹ * (f ω ^ 2) := by rw [cubeScale_sq]

-- N10iii
theorem scaledVec_add {d : ℕ} (f g : (Fin d → Bool) → ℝ) :
    scaledVec (fun ω => f ω + g ω) = scaledVec f + scaledVec g := by
  unfold scaledVec
  ext ω
  simp [mul_add]

-- N10iv
theorem scaledVec_norm_le {d : ℕ} (f : (Fin d → Bool) → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ((2 : ℝ) ^ d)⁻¹ * ∑ ω, f ω ^ 2 ≤ ρ ^ 2) :
    ‖scaledVec f‖ ≤ ρ := by
  have h2 : ‖scaledVec f‖^2 ≤ ρ^2 := by
    rw [scaledVec_norm_sq]
    exact h
  have habs := abs_le_of_sq_le_sq h2 hρ
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

end FunctionalAnalysis.GrothendieckInequalityWanted
end
