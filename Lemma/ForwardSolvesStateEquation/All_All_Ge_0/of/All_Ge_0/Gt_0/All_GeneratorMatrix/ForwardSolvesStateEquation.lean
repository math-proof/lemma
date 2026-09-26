import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Algebra.Order.Group.PosPart
import sympy.stats.generator_matrix
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.GeneratorMatrix.Sum_GetVecMul.eq.Zero.of.GeneratorMatrix
import Lemma.ForwardSolvesStateEquation.All_LtSlope.of.LtMul_GetVecMul.Ge_0.Gt_0.All_GeneratorMatrix.ForwardSolvesStateEquation
open Matrix Filter Topology


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {d : ℕ}
  {δ : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {θ : ℝ → EuclideanVec d}
  {μ : ℝ → S → ℝ}
-- given
  (h₀ : ForwardSolvesStateEquation δ Q θ μ)
  (h₁ : ∀ t, 0 ≤ t → GeneratorMatrix (Q (θ t)))
  (h₂ : 0 < δ)
  (h₃ : ∀ i, 0 ≤ μ 0 i) :
-- imply
  ∀ t, 0 ≤ t → ∀ i, 0 ≤ μ t i := by
-- proof
  intro T hT i
  let F : ℝ → ℝ := fun t => ∑ j, (μ t j)⁻
  have hFc : Continuous F := continuous_finsetSum _ fun j _ => ((continuous_apply j).comp h₀.cont).neg.max continuous_const
  have hF0 : F 0 ≤ 0 := by simp [F, negPart_eq_zero.2 (h₃ _)]
  have hbound : ∀ x ∈ Set.Ico 0 T, ∀ r, 0 < r → Filter.Frequently (fun z => slope F x z < r) (nhdsWithin x (Set.Ioi x)) := by
    intro x hx r hr
    have hc : (0 : ℝ) < Fintype.card S + 1 := by positivity
    have hε : 0 < r / (Fintype.card S + 1) := div_pos hr hc
    have hcoord : Filter.Eventually (fun z => ∀ j, slope (fun t => (μ t j)⁻) x z < δ⁻¹ * ((μ x)⁻ ᵥ* Q (θ x)) j + r / (Fintype.card S + 1)) (nhdsWithin x (Set.Ioi x)) :=
      eventually_all.2 fun j => ForwardSolvesStateEquation.All_LtSlope.of.LtMul_GetVecMul.Ge_0.Gt_0.All_GeneratorMatrix.ForwardSolvesStateEquation h₀ h₁ h₂ hx.1 (lt_add_of_pos_right _ hε)
    have hsum : ∑ j, δ⁻¹ * ((μ x)⁻ ᵥ* Q (θ x)) j = 0 := by
      rw [← Finset.mul_sum, GeneratorMatrix.Sum_GetVecMul.eq.Zero.of.GeneratorMatrix (h₁ x hx.1) _, mul_zero]
    refine (hcoord.mono fun z hz => ?_).frequently
    have hs : slope F x z = ∑ j, slope (fun t => (μ t j)⁻) x z := by
      simp only [F, slope_def_field, ← Finset.sum_div, Finset.sum_sub_distrib]
    rw [hs]
    calc
      _ ≤ ∑ j, (δ⁻¹ * ((μ x)⁻ ᵥ* Q (θ x)) j + r / (Fintype.card S + 1)) := Finset.sum_le_sum fun j _ => (hz j).le
      _ = Fintype.card S * (r / (Fintype.card S + 1)) := by
        rw [Finset.sum_add_distrib, hsum, zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ < r := by
        rw [show (Fintype.card S : ℝ) * (r / (Fintype.card S + 1)) = Fintype.card S * r / (Fintype.card S + 1) by ring, div_lt_iff₀ hc]
        nlinarith
  have hFle := image_le_of_liminf_slope_right_le_deriv_boundary (B := fun _ => (0 : ℝ)) (B' := fun _ => (0 : ℝ)) hFc.continuousOn hF0 continuousOn_const
    (fun x _ => hasDerivWithinAt_const x _ (0 : ℝ)) (fun x hx r hr => hbound x hx r hr) ⟨hT, le_rfl⟩
  have h1 : (μ T i)⁻ ≤ F T := Finset.single_le_sum (f := fun j => (μ T j)⁻) (fun j _ => negPart_nonneg _) (Finset.mem_univ i)
  exact negPart_eq_zero.1 (le_antisymm (h1.trans hFle) (negPart_nonneg _))


-- created on 2026-09-26
