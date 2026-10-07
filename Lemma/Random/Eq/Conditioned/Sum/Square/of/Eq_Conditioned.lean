import Mathlib.Probability.Independence.Basic
import sympy.stats.joint_rv
import sympy.Basic

open ProbabilityTheory MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → ℝ}
  {n : ℕ}
-- given
  (_ : ∀ i, Measurable (x i))
  (h : x n ⟂ᵢ[π] fun (ω : Ω) (i : Fin n) ↦ x i ω) :
-- imply
  x n ⟂ᵢ[π] fun ω ↦ ∑ i : Fin n, (x i ω)^2 := by
-- proof
  have hg : Measurable (fun v : Fin n → ℝ ↦ ∑ i : Fin n, (v i)^2) := by
    fun_prop
  have hcomp := h.comp measurable_id hg
  have heq : (fun v : Fin n → ℝ ↦ ∑ i : Fin n, (v i)^2) ∘ (fun ω i ↦ x i ω) = fun ω ↦ ∑ i : Fin n, (x i ω)^2 := rfl
  rw [heq] at hcomp
  exact hcomp


-- created on 2026-10-07
