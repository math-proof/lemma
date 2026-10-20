import Mathlib
import sympy.Basic
import sympy.atlas.Probability.KhintchineInequality
open scoped BigOperators
open scoped MeasureTheory
open MetaMathlibExt


/--
[khintchine_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/KhintchineInequality.lean)
-/
@[path]
private lemma khintchine_inequality_eq
  :
-- imply
  ∀ (p : ℝ), 0 < p →
    ∃ (A B : ℝ), 0 < A ∧ 0 < B ∧
    ∀ (N : ℕ) (a : Fin N → ℝ) (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (ε : Fin N → Ω → ℝ),
    (∀ i, Measurable (ε i)) →
    (∀ i, ∀ᵐ ω ∂μ, ε i ω = 1 ∨ ε i ω = -1) →
    (∀ i, MeasureTheory.integral μ (ε i) = 0) →
    ProbabilityTheory.iIndepFun ε μ →
    A * Real.sqrt (∑ i, (a i) ^ 2) ≤
    Real.rpow
    (MeasureTheory.integral μ (fun ω => Real.rpow |∑ i, a i * ε i ω| p))
    (1 / p) ∧
    Real.rpow
    (MeasureTheory.integral μ (fun ω => Real.rpow |∑ i, a i * ε i ω| p))
    (1 / p) ≤
    B * Real.sqrt (∑ i, (a i) ^ 2) := by
-- proof
  apply MetaMathlibExt.khintchine_inequality


-- created on 2026-10-20
