import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Algebra.Order.Group.PosPart
import sympy.stats.generator_matrix
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.GeneratorMatrix.NegGetVecMul.le.GetVecMul.of.Le_0.GeneratorMatrix
import Lemma.GeneratorMatrix.GetVecMul.ge.Zero.of.Ge_0.GeneratorMatrix
open Matrix Filter Topology


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {d : ℕ}
  {δ : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {θ : ℝ → EuclideanVec d}
  {μ : ℝ → S → ℝ}
  {x : ℝ}
  {r : ℝ}
  {i : S}
-- given
  (h₀ : ForwardSolvesStateEquation δ Q θ μ)
  (h₁ : ∀ t, 0 ≤ t → GeneratorMatrix (Q (θ t)))
  (h₂ : 0 < δ)
  (h₃ : 0 ≤ x)
  (h₄ : δ⁻¹ * ((μ x)⁻ ᵥ* Q (θ x)) i < r) :
-- imply
  Filter.Eventually (fun z => slope (fun t => (μ t i)⁻) x z < r) (nhdsWithin x (Set.Ioi x)) := by
-- proof
  have hd : HasDerivWithinAt (fun t => μ t i) (δ⁻¹ * (μ x ᵥ* Q (θ x)) i) (Set.Ioi x) x :=
    (hasDerivWithinAt_pi.1 (h₀.hasDeriv x h₃) i).Ioi_of_Ici
  have hc : ContinuousAt (fun t => μ t i) x := ((continuous_apply i).comp h₀.cont).continuousAt
  have hneg : -(δ⁻¹ * (μ x ᵥ* Q (θ x)) i) < r → Filter.Eventually (fun z => slope (fun t => -μ t i) x z < r) (nhdsWithin x (Set.Ioi x)) := fun h =>
    hd.neg.limsup_slope_le' (lt_irrefl x) h
  have hscale : ∀ {p q : ℝ}, p ≤ q → δ⁻¹ * p ≤ δ⁻¹ * q := fun h => mul_le_mul_of_nonneg_left h (inv_pos.2 h₂).le
  rcases lt_trichotomy (μ x i) 0 with hlt | heq | hgt
  · have hb : -(δ⁻¹ * (μ x ᵥ* Q (θ x)) i) ≤ δ⁻¹ * ((μ x)⁻ ᵥ* Q (θ x)) i := by
      rw [← mul_neg]
      exact hscale (GeneratorMatrix.NegGetVecMul.le.GetVecMul.of.Le_0.GeneratorMatrix (h₁ x h₃) hlt.le)
    filter_upwards [hneg (hb.trans_lt h₄), (hc.eventually_lt continuousAt_const hlt).filter_mono nhdsWithin_le_nhds] with z hz hz'
    rw [slope_def_field] at hz ⊢
    rw [negPart_eq_neg.2 hz'.le, negPart_eq_neg.2 hlt.le]
    exact hz
  · have hb0 : 0 ≤ δ⁻¹ * ((μ x)⁻ ᵥ* Q (θ x)) i := mul_nonneg (inv_pos.2 h₂).le (GeneratorMatrix.GetVecMul.ge.Zero.of.Ge_0.GeneratorMatrix (h₁ x h₃) heq.ge)
    have hb : -(δ⁻¹ * (μ x ᵥ* Q (θ x)) i) ≤ δ⁻¹ * ((μ x)⁻ ᵥ* Q (θ x)) i := by
      rw [← mul_neg]
      exact hscale (GeneratorMatrix.NegGetVecMul.le.GetVecMul.of.Le_0.GeneratorMatrix (h₁ x h₃) heq.le)
    filter_upwards [hneg (hb.trans_lt h₄), self_mem_nhdsWithin] with z hz hzx
    have hzx' : 0 < z - x := sub_pos.2 hzx
    rw [slope_def_field] at hz ⊢
    rw [heq, negPart_zero, sub_zero, negPart_def, div_lt_iff₀ hzx']
    rw [heq, div_lt_iff₀ hzx'] at hz
    exact max_lt (by linarith) (mul_pos (hb0.trans_lt h₄) hzx')
  · have hb0 : 0 ≤ δ⁻¹ * ((μ x)⁻ ᵥ* Q (θ x)) i := mul_nonneg (inv_pos.2 h₂).le (GeneratorMatrix.GetVecMul.ge.Zero.of.Ge_0.GeneratorMatrix (h₁ x h₃) hgt.le)
    filter_upwards [(continuousAt_const.eventually_lt hc hgt).filter_mono nhdsWithin_le_nhds] with z hz
    rw [slope_def_field, negPart_eq_zero.2 hz.le, negPart_eq_zero.2 hgt.le, sub_zero, zero_div]
    exact hb0.trans_lt h₄


-- created on 2026-09-26
