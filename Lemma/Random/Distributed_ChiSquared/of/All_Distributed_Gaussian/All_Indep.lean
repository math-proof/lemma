import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Algebra.BigOperators.Fin
import Notation.Fun
import Notation.Probability.HasLaw
import Notation.Algebra.Power
import Def.Probability.ChiSquared
import Lemma.Measure.SumSqGaussians.eq.ChiSquaredReal
import Instance.Probability.Process.HiddenMarkovSequence
open MeasureTheory ProbabilityTheory
open Fun
open Measure


/--
Independent standard normals have sum of squares distributed as 𝒳² with `n` degrees of freedom.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {n : ℕ}
  {x : ℕ ⇀ Ω → ℝ}
-- given
  (h₀ : ∀ k, x[k] ⟂ᵢ[π] x[:k])
  (h₁ : ∀ k, x[k] ∼[π] gaussianReal 0 1) :
-- imply
  ∑ i : Fin n, x[i]² ∼[π] chiSquaredReal n := by
-- proof
  have hvec : HasLaw (fun ω (i : Fin n) ↦ x[i] ω)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) π := by
    induction n with
    | zero =>
      have heq : (fun ω (i : Fin 0) ↦ x[i] ω) = fun _ ↦ (isEmptyElim : Fin 0 → ℝ) := by
        funext ω i; apply i.elim0
      rw [heq]
      refine ⟨measurable_const.aemeasurable, ?_⟩
      rw [Measure.map_const, Measure.pi_of_empty, measure_univ, one_smul]
    | succ n ih =>
      have hx : (x[:n] : Ω → Fin n → ℝ) = fun ω (i : Fin n) ↦ x[i] ω := by
        funext ω i; rfl
      have hprefix : HasLaw x[:n] (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) π := by
        rwa [hx]
      have hprod := (h₀ n).symm.hasLaw_prod hprefix (h₁ n)
      have hY : HasLaw (Prod.swap : (Fin n → ℝ) × ℝ → ℝ × (Fin n → ℝ))
        ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1))
        ((Measure.pi fun _ : Fin n ↦ gaussianReal 0 1).prod (gaussianReal 0 1)) :=
        ⟨measurable_swap.aemeasurable, Measure.prod_swap⟩
      have hswap : HasLaw (fun ω ↦ (x[n] ω, x[:n] ω))
        ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1)) π :=
        hY.fun_comp hprod
      have hmp :=
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) (Fin.last n)).symm
      have hlaw := hmp.hasLaw.fun_comp hswap
      have hsnoc : (fun ω (i : Fin (n + 1)) ↦ x[i] ω) =
          fun ω ↦ Fin.snoc (x[:n] ω) (x[n] ω) := by
        funext ω i
        refine Fin.lastCases ?_ ?_ i
        ·
          rw [Fin.snoc_last]
          rfl
        ·
          intro j
          rw [Fin.snoc_castSucc, hx]
          rfl
      rw [hsnoc]
      convert hlaw using 1
      funext ω
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last]
      rfl
  have hsq_map : HasLaw (fun v : Fin n → ℝ ↦ ∑ i, (v i) ^ 2) (sumSqGaussians n)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
    unfold sumSqGaussians
    apply hasLaw_map (Continuous.aemeasurable (by continuity))
  have hchar : sumSqGaussians n = chiSquaredReal n :=
    SumSqGaussians.eq.ChiSquaredReal n
  have hsq : HasLaw (fun v : Fin n → ℝ ↦ ∑ i, (v i) ^ 2) (chiSquaredReal n)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
    rwa [← hchar]
  have hcomp : (∑ i : Fin n, x[i]²) =
      (fun v : Fin n → ℝ ↦ ∑ i, (v i) ^ 2) ∘ (fun ω (i : Fin n) ↦ x[i] ω) := by
    funext ω
    simp [Function.comp_apply, Finset.sum_apply, Pi.pow_apply]
  rw [hcomp]
  apply hsq.fun_comp hvec


-- created on 2021-07-17
-- updated on 2026-10-30
