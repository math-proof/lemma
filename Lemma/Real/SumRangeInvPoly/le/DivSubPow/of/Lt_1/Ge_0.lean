import sympy.stats.step_size
import sympy.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Finset Real


@[main]
private lemma main
  {ν : ℝ}
  {a : ℕ}
-- given
  (h₀ : 0 ≤ ν)
  (h₁ : ν < 1) :
-- imply
  ∑ k ∈ range a, inv_poly ν 2 k ≤ (((a : ℝ) + 1) ^ (1 - ν) - 1) / (1 - ν) := by
-- proof
  have hf : AntitoneOn (fun x : ℝ => (x + 1) ^ (-ν)) (Set.Icc 0 (0 + a)) := by
    intro x hx y hy hxy
    exact rpow_le_rpow_of_nonpos (by linarith [hx.1]) (by linarith) (by linarith)
  have h := hf.sum_le_integral
  simp only [zero_add] at h
  rw [intervalIntegral.integral_comp_add_right (fun x : ℝ => x ^ (-ν)),
    integral_rpow (Or.inl (by linarith))] at h
  convert h using 1
  · refine sum_congr rfl fun i _ => ?_
    simp only [inv_poly]
    push_cast
    ring_nf
  · norm_num
    ring_nf


-- created on 2026-09-26