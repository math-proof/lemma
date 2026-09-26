import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Algebra.Order.Group.PosPart
import sympy.stats.generator_matrix
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.ForwardSolvesStateEquation.All_All_Ge_0.of.All_Ge_0.Gt_0.All_GeneratorMatrix.ForwardSolvesStateEquation
import Lemma.ForwardSolvesStateEquation.All_EqSumSum.of.All_GeneratorMatrix.ForwardSolvesStateEquation
import Lemma.ForwardSolvesStateEquation.ForwardSolvesStateEquation_Sub.of.ForwardSolvesStateEquation.ForwardSolvesStateEquation
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {d : ℕ}
  {δ : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {θ : ℝ → EuclideanVec d}
  {μ : ℝ → S → ℝ}
  {ν : ℝ → S → ℝ}
-- given
  (h₀ : ForwardSolvesStateEquation δ Q θ μ)
  (h₁ : ForwardSolvesStateEquation δ Q θ ν)
  (h₂ : ∀ t, 0 ≤ t → GeneratorMatrix (Q (θ t)))
  (h₃ : 0 < δ)
  (h₄ : μ 0 = ν 0) :
-- imply
  Set.EqOn μ ν (Set.Ici 0) := by
-- proof
  intro t ht
  have hξ := ForwardSolvesStateEquation.ForwardSolvesStateEquation_Sub.of.ForwardSolvesStateEquation.ForwardSolvesStateEquation h₀ h₁
  have hnn := ForwardSolvesStateEquation.All_All_Ge_0.of.All_Ge_0.Gt_0.All_GeneratorMatrix.ForwardSolvesStateEquation hξ h₂ h₃ (fun i => by simp [h₄]) t ht
  have hm := ForwardSolvesStateEquation.All_EqSumSum.of.All_GeneratorMatrix.ForwardSolvesStateEquation hξ h₂ t ht
  simp only [Pi.sub_apply, h₄, sub_self, Finset.sum_const_zero] at hm
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 hm
  funext i
  have := hz i (Finset.mem_univ i)
  simp only [Pi.sub_apply] at this
  linarith


-- created on 2026-09-26
