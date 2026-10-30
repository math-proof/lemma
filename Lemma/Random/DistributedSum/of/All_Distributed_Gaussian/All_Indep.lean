import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Algebra.BigOperators.Fin
import Notation.Fun
import Notation.Probability.HasLaw
import Notation.Algebra.Power
import Instance.Probability.Process.HiddenMarkovSequence
import Lemma.Random.DistributedAdd.of.Distributed_Gaussian.Distributed_Gaussian.Indep
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Fun Random
open scoped NNReal


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {n : ℕ}
  {x : ℕ ⇀ Ω → ℝ}
  {μ : ℕ ⇀ ℝ} {σ : ℕ ⇀ NNReal}
-- given
  (h₀ : ∀ k, x[k] ⟂ᵢ[π] x[:k])
  (h₁ : ∀ k, x[k] ∼[π] gaussianReal μ[k] σ[k]²) :
-- imply
  ∑ k : Fin n, x[k] ∼[π] gaussianReal (∑ k : Fin n, μ[k]) (∑ k : Fin n, σ[k]²) := by
-- proof
  induction n with
  | zero =>
    refine ⟨measurable_const.aemeasurable, ?_⟩
    change π.map (fun _ : Ω ↦ (0 : ℝ)) = gaussianReal 0 0
    simp [Measure.map_const, gaussianReal_zero_var]
  | succ n ih =>
    have hsum :
      (∑ k : Fin (n + 1), x[k]) =
        (∑ k : Fin n, x[k]) + x[n] := by
      funext ω
      simp only [Pi.add_apply]
      rw [Fin.sum_univ_castSucc]
      simp [Fin.val_castSucc, Fin.val_last]
    have hμ :
      (∑ k : Fin (n + 1), μ[k]) =
        (∑ k : Fin n, μ[k]) + μ[n] := by
      rw [Fin.sum_univ_castSucc]
      simp [Fin.val_castSucc, Fin.val_last]
    have hσ :
      (∑ k : Fin (n + 1), σ[k]²) =
        (∑ k : Fin n, σ[k]²) + σ[n]² := by
      rw [Fin.sum_univ_castSucc]
      simp [Fin.val_castSucc, Fin.val_last]
    rw [hsum, hμ, hσ]
    have h_indep : x[n] ⟂ᵢ[π] (∑ k : Fin n, x[k]) := by
      have hx : (∑ k : Fin n, x[k]) =
          (fun y : Fin n → ℝ ↦ ∑ i, y i) ∘ x[:n] := by
        ext ω
        simp only [Function.comp_apply, Finset.sum_apply]
        refine Fintype.sum_congr _ _ fun i ↦ ?_
        rfl
      rw [hx]
      exact (h₀ n).comp measurable_id (Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _)
    set σ₀ : NNReal := NNReal.sqrt (∑ k : Fin n, σ[k]²)
    have hσ₀ : σ₀² = ∑ k : Fin n, σ[k]² := NNReal.sq_sqrt _
    have ih' :
      (∑ k : Fin n, x[k]) ∼[π] gaussianReal (∑ k : Fin n, μ[k]) σ₀² := by
      rwa [hσ₀]
    have hadd := DistributedAdd.of.Distributed_Gaussian.Distributed_Gaussian.Indep
      h_indep.symm ih' (h₁ n)
    rwa [hσ₀] at hadd


-- created on 2021-07-25
-- updated on 2026-10-30
