import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM17.Lagrangian
open Real Set MeasureTheory CM17Lagrangian


namespace CM17Lagrangian

/--
[ibp_fundamental_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Lagrangian.lean)
-/
@[path]
lemma ibp_fundamental_lemma
  {n : ℕ}
  {f : Spacetime n → ℝ}
-- given
  (hf_cont : Continuous f)
  (hf : ∀ (K : Set (Spacetime n)), IsCompact K → ∀ (ψ : ScalarField n), IsVariation K ψ → ∫ x in K, f x * ψ x = 0) :
-- imply
  ∀ x : Spacetime n, f x = 0 := by
-- proof
  set_option maxHeartbeats 800000 in
  by_contra h
  push Not at h
  obtain ⟨x₀, hx₀⟩ := h
  have hcont_at := hf_cont.continuousAt (x := x₀)
  have habs_pos : 0 < |f x₀| := abs_pos.mpr hx₀
  obtain ⟨δ, hδ_pos, hδ_ball⟩ :=
    Metric.continuousAt_iff.mp hcont_at (|f x₀|) habs_pos
  set rIn := δ / 4 with _hrIn_def
  set rOut := δ / 2 with _hrOut_def
  have hrIn_pos : 0 < rIn := by positivity
  have hrIn_lt_rOut : rIn < rOut := by linarith
  set b : ContDiffBump x₀ := ⟨rIn, rOut, hrIn_pos, hrIn_lt_rOut⟩
  have hb_smooth : ContDiff ℝ (⊤ : ℕ∞) (b : Spacetime n → ℝ) := b.contDiff
  have hb_supp_eq : Function.support (b : Spacetime n → ℝ) = Metric.ball x₀ rOut := b.support_eq
  have hb_supp_sub_delta : Function.support (b : Spacetime n → ℝ) ⊆ Metric.ball x₀ δ := by
    rw [hb_supp_eq]; exact Metric.ball_subset_ball (by linarith)
  have hb_compact : HasCompactSupport (b : Spacetime n → ℝ) := b.hasCompactSupport
  have hb_nonneg : ∀ y, 0 ≤ (b : Spacetime n → ℝ) y := fun y => b.nonneg
  have hb_x₀ : (b : Spacetime n → ℝ) x₀ = 1 := by
    apply b.one_of_mem_closedBall
    simp [Metric.mem_closedBall, dist_self]
    exact le_of_lt hrIn_pos
  have hf_sign : ∀ y ∈ Metric.ball x₀ δ, f x₀ * f y > 0 := by
    intro y hy
    have hclose := hδ_ball hy
    rw [Real.dist_eq] at hclose
    obtain hneg | hpos := lt_or_gt_of_ne hx₀
    ·
      have : f y < 0 := by
        have := abs_lt.mp hclose
        linarith [abs_of_neg hneg]
      exact mul_pos_of_neg_of_neg hneg this
    ·
      have : f y > 0 := by
        have := abs_lt.mp hclose
        linarith [abs_of_pos hpos]
      exact mul_pos hpos this
  set ψ := fun y => f x₀ * (b : Spacetime n → ℝ) y with hψ_def
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := hb_smooth.const_smul (f x₀)
  have hψ_supp : Function.support ψ = Function.support (b : Spacetime n → ℝ) := by
    simp [hψ_def, Function.support, hx₀]
  set K := Metric.closedBall x₀ δ
  have hK : IsCompact K := isCompact_closedBall x₀ δ
  have hψ_var : IsVariation K ψ := by
    constructor
    · exact hψ_smooth
    · rw [hψ_supp]
      exact hb_supp_sub_delta.trans Metric.ball_subset_closedBall
  have hint := hf K hK ψ hψ_var
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at hint
  ·
    have heq : ∫ x, f x * ψ x = f x₀ * ∫ x, f x * (b : Spacetime n → ℝ) x := by
      simp only [hψ_def]
      rw [show (fun x => f x * (f x₀ * (b : Spacetime n → ℝ) x)) =
        (fun x => f x₀ • (f x * (b : Spacetime n → ℝ) x)) from by ext; rw [smul_eq_mul]; ring]
      rw [integral_smul, smul_eq_mul]
    rw [heq] at hint
    have hint' : ∫ x, f x * (b : Spacetime n → ℝ) x = 0 :=
      (mul_eq_zero.mp hint).resolve_left hx₀
    have hg_cont : Continuous (fun x => f x₀ * f x * (b : Spacetime n → ℝ) x) :=
      (continuous_const.mul hf_cont).mul b.continuous
    have hg_compact : HasCompactSupport (fun x => f x₀ * f x * (b : Spacetime n → ℝ) x) := by
      have : (fun x => f x₀ * f x * (b : Spacetime n → ℝ) x) =
        (fun x => (f x₀ * f x) * (b : Spacetime n → ℝ) x) := by ext; ring
      rwa [this]
    have hg_nonneg : 0 ≤ (fun x => f x₀ * f x * (b : Spacetime n → ℝ) x) := by
      intro x
      by_cases hxb : (b : Spacetime n → ℝ) x = 0
      · simp [hxb]
      · have hx_supp : x ∈ Function.support (b : Spacetime n → ℝ) := Function.mem_support.mpr hxb
        have hx_ball : x ∈ Metric.ball x₀ δ := hb_supp_sub_delta hx_supp
        exact mul_nonneg (le_of_lt (hf_sign x hx_ball)) (hb_nonneg x)
    have hg_x₀ : (fun x => f x₀ * f x * (b : Spacetime n → ℝ) x) x₀ ≠ 0 := by
      simp [hb_x₀]
      exact hx₀
    have hg_pos := @Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      _ _ _ _ (volume : Measure (Spacetime n)) _ _ _ x₀
      hg_cont hg_compact hg_nonneg hg_x₀
    have hg_eq : ∫ x, (fun x => f x₀ * f x * (b : Spacetime n → ℝ) x) x =
      f x₀ * ∫ x, f x * (b : Spacetime n → ℝ) x := by
      rw [show (fun x => f x₀ * f x * (b : Spacetime n → ℝ) x) =
        (fun x => f x₀ • (f x * (b : Spacetime n → ℝ) x)) from by ext; rw [smul_eq_mul]; ring]
      rw [integral_smul, smul_eq_mul]
    rw [hg_eq, hint'] at hg_pos
    simp at hg_pos
  ·
    intro x hx
    simp only [hψ_def]
    have : (b : Spacetime n → ℝ) x = 0 := by
      by_contra hbx
      have : x ∈ Function.support (b : Spacetime n → ℝ) := Function.mem_support.mpr hbx
      have : x ∈ K := (hb_supp_sub_delta.trans Metric.ball_subset_closedBall) this
      exact hx this
    simp [this]
/-- Smooth differentiation under the integral sign on a compact domain: if at $\varepsilon_0$
the parameter derivative $\partial_{\varepsilon} F(\varepsilon, x)$ exists pointwise with
limit $F'(x)$ and both $F(\varepsilon, \cdot)$ and $F'$ are continuous on $K$, then the
parameterized integral $\varepsilon \mapsto \int_K F(\varepsilon, x) \, dx$ has derivative
$\int_K F'(x) \, dx$ at $\varepsilon_0$. -/

end CM17Lagrangian


-- created on 2026-10-23
