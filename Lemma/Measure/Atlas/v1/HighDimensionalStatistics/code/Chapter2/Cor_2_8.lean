import Mathlib
import sympy.Basic
open Matrix Finset BigOperators MeasureTheory Real


/--
[cor_2_8_mse_prob](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Cor_2_8.lean)
-/
@[path]
lemma cor_2_8_mse_prob
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {θhat : Ω → Fin d → ℝ}
  {k : ℕ}
  {σ : ℝ}
  {δ : ℝ}
-- given
  (hn : 0 < n)
  (hk : 1 ≤ k)
  (hkd : 2 * k ≤ d)
  (hσ : 0 < σ)
  (hδ_pos : 0 < δ)
  (hδ_le : δ ≤ 1)
  (hhat_sparse : ∀ ω, (univ.filter (fun j => θhat ω j ≠ 0)).card ≤ k)
  (hstar_sparse : (univ.filter (fun j => θstar j ≠ 0)).card ≤ k)
  (hLS : ∀ ω, ∀ θ : Fin d → ℝ, (univ.filter (fun j => θ j ≠ 0)).card ≤ k → dotProduct ((X.mulVec θstar + ε ω) - X.mulVec (θhat ω)) ((X.mulVec θstar + ε ω) - X.mulVec (θhat ω)) ≤ dotProduct ((X.mulVec θstar + ε ω) - X.mulVec θ) ((X.mulVec θstar + ε ω) - X.mulVec θ))
  (hsubG : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ ∧ ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤ Real.exp (s ^ 2 * σ ^ 2 / 2)) :
-- imply
  μ {ω | (1 / (n : ℝ)) * dotProduct (X.mulVec (θhat ω - θstar)) (X.mulVec (θhat ω - θstar)) ≤ 32 * σ ^ 2 / ↑n * (2 * ↑k * Real.log (Real.exp 1 * ↑d / (2 * ↑k)) + 2 * ↑k * Real.log 6 + Real.log (1 / δ))} ≥ ENNReal.ofReal (1 - δ) :=
-- proof
  thm_2_6_sparse_ls_high_prob hn X θstar ε θhat k hk hkd σ hσ δ hδ_pos hδ_le
    hhat_sparse hstar_sparse hLS hsubG


-- created on 2026-10-23
