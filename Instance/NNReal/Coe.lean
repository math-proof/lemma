import Notation.Lean.Expr.Singleton
import Notation.Algebra.Power
import Mathlib.Basic.NNReal.Defs

/-- {σ : ℝ⁺} as NNReal via ⟨σ.1, σ.2.le⟩. -/
instance : Coe ℝ⁺ NNReal where
  coe σ := ⟨σ.1, le_of_lt σ.2⟩

/-- Constant random variable: {σ : ℝ⁺} as Ω → ℝ via Function.const Ω (σ : ℝ).

Lets ANOVA leaves write ((σ : ℝ⁺) : Ω → ℝ) / ((σ : ℝ⁺)² : Ω → ℝ)
instead of Function.const Ω (σ : ℝ) / Function.const Ω ((σ : ℝ) ^ 2).
σ² is Notation.Algebra.Power (x² → x ^ 2). The squared form elaborates by
coercing σ first (expected type Ω → ℝ), then pointwise Pow on Ω → ℝ —
no general Coe ℝ (Ω → ℝ). -/
instance {Ω : Type*} : Coe ℝ⁺ (Ω → ℝ) where
  coe σ := Function.const Ω (σ : ℝ)
