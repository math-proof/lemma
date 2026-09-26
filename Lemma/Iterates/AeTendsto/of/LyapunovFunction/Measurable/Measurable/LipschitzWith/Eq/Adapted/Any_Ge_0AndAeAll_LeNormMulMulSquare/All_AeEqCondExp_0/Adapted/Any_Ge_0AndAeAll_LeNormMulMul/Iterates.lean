import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Process.Adapted
import sympy.stats.iterates
import sympy.stats.lyapunov
import sympy.stats.step_size
import sympy.stats.filtration
import sympy.Basic
import Lemma.Iterates.Any_Any_AeAll_LeUFnSub.of.LyapunovFunction.SummableSquare.All_Gt_0.Any_LipschitzWith.Eq.Any_Ge_0AndAeAll_LeNormMulMulSquare.Any_Ge_0AndAeAll_LeNormMulMul.Iterates
import Lemma.Iterates.Any_Ge_0AndAeLeNorm.of.All_Gt_0.Any_LipschitzWith.Any_Ge_0AndAeAll_LeNormMulMulSquare.Any_Ge_0AndAeAll_LeNormMulMul.Iterates
import Lemma.Random.All_Tendsto_0.of.Any_All_AeLeCondExp.Summable.TendstoSum.All_Gt_0.All_AeGe_0.All_Integrable.StronglyAdapted
import Lemma.Random.CondExpInner.ae.Inner_CondExp.of.All_AEStronglyMeasurable.All_Integrable_Mul.Integrable
open Filter MeasureTheory Finset Topology Iterates Random
open scoped RealInnerProductSpace


@[main]
private lemma main
  {d : ℕ}
  {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀}
  {x e₁ e₂ : ℕ → Ω → EuclideanVec d}
  {x₀ z : EuclideanVec d}
  {f : EuclideanVec d → EuclideanVec d}
  {α : ℕ → ℝ} [RobbinsMonro α]
  {L : NNReal}
  {φ : EuclideanVec d → ℝ}
  {φ' : EuclideanVec d → EuclideanVec d}
-- given
  (h₀ : Iterates x x₀ f e₁ e₂ α)
  (h₁ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n, ‖e₁ (n + 1) ω‖ ≤ C * α n * (‖x n ω‖ + 1))
  (h₂ : Adapted (ℱ.shift 1) fun n => e₁ (n + 1))
  (h₃ : ∀ n, μ[e₁ (n + 1) | ℱ n] =ᵐ[μ] 0)
  (h₄ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n, ‖e₂ (n + 1) ω‖ ≤ C * α n ^ 2 * (‖x n ω‖ + 1))
  (h₅ : Adapted (ℱ.shift 1) fun n => e₂ (n + 1))
  (h₆ : z = f z)
  (h₇ : LipschitzWith L f)
  (h₈ : Measurable φ)
  (h₉ : Measurable φ')
  (h₁₀ : LyapunovFunction φ φ' f) :
-- imply
  ∀ᵐ ω ∂μ, Tendsto (fun n => x n ω) atTop (𝓝 z) := by
-- proof
  have hα : ∀ n, 0 < α n := RobbinsMonro.pos
  obtain ⟨B₁, B₂, hB₁, hB₂, n₀, hfund⟩ :=
    Any_Any_AeAll_LeUFnSub.of.LyapunovFunction.SummableSquare.All_Gt_0.Any_LipschitzWith.Eq.Any_Ge_0AndAeAll_LeNormMulMulSquare.Any_Ge_0AndAeAll_LeNormMulMul.Iterates h₀ h₁ h₄ h₆ ⟨L, h₇⟩ hα (RobbinsMonro.sqsum (α := α)) h₁₀
  have hbdd := Any_Ge_0AndAeLeNorm.of.All_Gt_0.Any_LipschitzWith.Any_Ge_0AndAeAll_LeNormMulMulSquare.Any_Ge_0AndAeAll_LeNormMulMul.Iterates h₀ h₁ h₄ ⟨L, h₇⟩ hα
  obtain ⟨C₀, hC₀, hnorm⟩ := h₁₀.norm_le
  obtain ⟨C₁, hC₁, hle⟩ := h₁₀.le_norm
  obtain ⟨C₂, hC₂, hinner⟩ := h₁₀.inner_grad_le'
  obtain ⟨C₃, hC₃, he₁⟩ := h₁
  have hxm : ∀ n, Measurable[ℱ n] (x n) := by
    intro n
    induction n with
    | zero =>
      rw [show x 0 = fun _ => x₀ from funext h₀.init]
      exact measurable_const
    | succ n ih =>
      have ih' := ih.mono (ℱ.mono n.le_succ) le_rfl
      rw [show x (n + 1) = fun ω => x n ω + α n • (f (x n ω) - x n ω) + e₁ (n + 1) ω + e₂ (n + 1) ω from funext (h₀.step n)]
      exact ((ih'.add (((h₇.continuous.measurable.comp ih').sub ih').const_smul (α n))).add (h₂ n)).add (h₅ n)
  have hint : ∀ k, Integrable (fun ω => φ (x k ω - z)) μ := by
    intro k
    obtain ⟨C, hC, hx⟩ := hbdd k
    apply Integrable.of_bound (h₈.comp (((hxm k).mono (ℱ.le k) le_rfl).sub_const z)).aestronglyMeasurable ((C₁ * (C + ‖z‖)) ^ 2)
    filter_upwards [hx] with ω hω
    rw [Function.comp_apply, Real.norm_of_nonneg (h₁₀.nonneg _), ← Real.sq_sqrt (h₁₀.nonneg (x k ω - z))]
    gcongr
    exact (hle _).trans (by gcongr; exact (norm_sub_le _ _).trans (by linarith))
  have hstep : ∀ k ≥ n₀, ∀ᵐ ω ∂μ, μ[fun ω' => φ (x (k + 1) ω' - z) | ℱ k] ω ≤ (1 - B₁ * α k) * φ (x k ω - z) + B₂ * α k ^ 2 := by
    intro k hk
    obtain ⟨C, hC, hx⟩ := hbdd k
    have hαk := hα k
    have he₁int : Integrable (e₁ (k + 1)) μ := by
      apply Integrable.of_bound ((h₂ k).mono (ℱ.le (k + 1)) le_rfl).aestronglyMeasurable (C₃ * α k * (C + 1))
      filter_upwards [he₁, hx] with ω h₁ h₂
      exact (h₁ k).trans (by gcongr)
    have hmeas : ∀ i, AEStronglyMeasurable[ℱ k] (fun ω => φ' (x k ω - z) i) μ := fun i =>
      ((EuclideanSpace.proj i).continuous.measurable.comp (h₉.comp ((hxm k).sub_const z))).aestronglyMeasurable
    have hprod : ∀ i, Integrable ((fun ω => φ' (x k ω - z) i) * fun ω => e₁ (k + 1) ω i) μ := by
      intro i
      apply Integrable.of_bound (((hmeas i).mono (ℱ.le k)).mul ((EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable he₁int.1)) (C₂ * (C₁ * (C + ‖z‖)) * (C₁ * (C₃ * α k * (C + 1))))
      filter_upwards [he₁, hx] with ω h₁ h₂
      calc
        _ = |φ' (x k ω - z) i| * |e₁ (k + 1) ω i| := abs_mul _ _
        _ ≤ ∑ j, |φ' (x k ω - z) j| * |e₁ (k + 1) ω j| :=
          single_le_sum (f := fun j => |φ' (x k ω - z) j| * |e₁ (k + 1) ω j|) (fun j _ => by positivity) (mem_univ i)
        _ ≤ C₂ * √(φ (x k ω - z)) * √(φ (e₁ (k + 1) ω)) := hinner _ _
        _ ≤ _ := by
          gcongr
          · exact (hle _).trans (by gcongr; exact (norm_sub_le _ _).trans (by linarith))
          · exact (hle _).trans (by gcongr; exact (h₁ k).trans (by gcongr))
    have hinnerInt : Integrable (fun ω => ⟪φ' (x k ω - z), e₁ (k + 1) ω⟫) μ :=
      (integrable_finsetSum univ fun i _ => hprod i).congr (ae_of_all _ fun ω => by simp [PiLp.inner_apply, mul_comm])
    have ha : Integrable (fun ω => (1 - B₁ * α k) * φ (x k ω - z)) μ := (hint k).const_mul _
    have hc : Integrable (fun _ : Ω => B₂ * α k ^ 2) μ := integrable_const _
    refine (condExp_mono (hint (k + 1)) ((ha.add hinnerInt).add hc) (by filter_upwards [hfund] with ω hω using hω k hk)).trans_eq ?_
    filter_upwards [condExp_add (ha.add hinnerInt) hc (ℱ k), condExp_add ha hinnerInt (ℱ k), CondExpInner.ae.Inner_CondExp.of.All_AEStronglyMeasurable.All_Integrable_Mul.Integrable he₁int hprod hmeas, h₃ k] with ω h₁ h₂ h₃ h₄
    rw [h₁, Pi.add_apply, h₂, Pi.add_apply, h₃, h₄, condExp_of_stronglyMeasurable (f := fun ω => (1 - B₁ * α k) * φ (x k ω - z)) (ℱ.le k) (((h₈.comp ((hxm k).sub_const z)).const_mul _).stronglyMeasurable) ha, condExp_const (ℱ.le k)]
    simp
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => φ (x (n + n₀) ω - z)) atTop (𝓝 0) := by
    apply All_Tendsto_0.of.Any_All_AeLeCondExp.Summable.TendstoSum.All_Gt_0.All_AeGe_0.All_Integrable.StronglyAdapted (ℱ := ℱ.shift n₀) (f := fun n ω => φ (x (n + n₀) ω - z)) (T := fun n => B₁ * α (n + n₀))
    · intro n
      exact (h₈.comp ((hxm (n + n₀)).sub_const z)).stronglyMeasurable
    · exact fun n => hint (n + n₀)
    · exact fun n => ae_of_all _ fun ω => h₁₀.nonneg _
    · exact fun n => mul_pos hB₁ (hα _)
    · refine ((tendsto_atTop_add_const_right atTop (-∑ k ∈ range n₀, α k) ((tendsto_add_atTop_iff_nat n₀).2 (RobbinsMonro.sum (α := α)))).const_mul_atTop hB₁).congr fun n => ?_
      rw [← mul_sum, add_comm n n₀, sum_range_add]
      simp only [add_comm n₀]
      ring
    · simpa [mul_pow] using ((summable_nat_add_iff n₀).2 (RobbinsMonro.sqsum (α := α))).mul_left (B₁ ^ 2)
    · refine ⟨B₂ / B₁ ^ 2, by positivity, fun n => ?_⟩
      filter_upwards [hstep (n + n₀) (by omega)] with ω hω
      show μ[fun ω => φ (x (n + 1 + n₀) ω - z) | ℱ (n + n₀)] ω ≤ _
      rw [Nat.add_right_comm]
      apply hω.trans_eq
      field_simp
  filter_upwards [hlim] with ω hω
  have h := ((tendsto_add_atTop_iff_nat (f := fun n => φ (x n ω - z)) n₀).1 hω).sqrt.const_mul C₀
  rw [Real.sqrt_zero, mul_zero] at h
  exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun n => hnorm _) h)


-- created on 2026-09-26