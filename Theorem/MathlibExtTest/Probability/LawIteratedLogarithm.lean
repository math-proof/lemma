/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Probability/LawIteratedLogarithm.lean -/


import Def.Probability.LawIteratedLogarithm
import Lemma.Measure.LawIteratedLogarithm
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory


namespace MathlibExtTest.Probability.LawIteratedLogarithm

-- Reflecting an i.i.d. family preserves the hypotheses and instantiates the theorem.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (X n))
    (hIndep : iIndepFun X μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ)
    (hMean : μ[X 0] = 0)
    (hVar : Var[X 0; μ] = 1) :
    ∀ᵐ ω ∂μ,
      Filter.limsup (fun n : ℕ ↦
        (∑ i ∈ Finset.range n, -X i ω) /
          Real.sqrt (2 * (n : ℝ) * Real.log (Real.log (n : ℝ)))) Filter.atTop = (1 : ℝ)
      ∧ Filter.liminf (fun n : ℕ ↦
        (∑ i ∈ Finset.range n, -X i ω) /
          Real.sqrt (2 * (n : ℝ) * Real.log (Real.log (n : ℝ)))) Filter.atTop = (-1 : ℝ) := by
  let Y : ℕ → Ω → ℝ := fun n ↦ -X n
  have hY (n : ℕ) : Y n = (fun x : ℝ ↦ -x) ∘ X n := by
    funext ω
    simp only [Y, Pi.neg_apply, Function.comp_apply]
  have hYindep : iIndepFun Y μ := by
    rw [show Y = fun n ↦ (fun x : ℝ ↦ -x) ∘ X n by
      funext n
      exact hY n]
    exact hIndep.comp (fun _ : ℕ ↦ fun x : ℝ ↦ -x) (fun _ ↦ measurable_neg)
  have hYident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := by
    intro i
    rw [hY i, hY 0]
    exact (hIdent i).comp measurable_neg
  have hYmean : μ[Y 0] = 0 := by
    change (∫ ω, -X 0 ω ∂μ) = 0
    rw [integral_neg, hMean, neg_zero]
  have hYvar : Var[Y 0; μ] = 1 := by
    change Var[fun ω ↦ -X 0 ω; μ] = 1
    rw [variance_fun_neg, hVar]
  have h :=
    MathlibExt.Probability.LawIteratedLogarithmWanted.law_of_the_iterated_logarithm_of_memLp
      Y (fun n ↦ (hMeas n).neg) hYindep hYident
      (by simpa only [Y] using hMemLp.neg) hYmean hYvar
  simpa only [Y, Pi.neg_apply] using h

end MathlibExtTest.Probability.LawIteratedLogarithm
