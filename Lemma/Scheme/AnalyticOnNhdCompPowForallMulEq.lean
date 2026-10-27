import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Complex_exists_analyticOnNhd_comp_pow_of_forall_mul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Complex_exists_analyticOnNhd_comp_pow_of_forall_mul_eq.lean)
-/
@[path]
private lemma main
  {e : ℕ}
  {ω : ℂ}
  {f : ℂ → ℂ}
  {r : ℝ}
  -- given
  (he : 0 < e)
  (hω : IsPrimitiveRoot ω e)
  (hr : 0 < r)
  (hf : AnalyticOnNhd ℂ f (Metric.ball 0 r))
  (hinv : ∀ z ∈ Metric.ball 0 r, f (ω * z) = f z) :
  -- imply
  ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 (r ^ e)) ∧ ∀ z ∈ Metric.ball 0 r, f z = F (z ^ e) := by
  -- proof
  classical
  let _ : NeZero e := NeZero.of_pos he
  have he0 : e ≠ 0 := he.ne'
  have hω1 : ‖ω‖ = 1 := hω.norm'_eq_one he0
  have hinvj : ∀ (j : ℕ), ∀ z ∈ Metric.ball (0 : ℂ) r, f (ω ^ j * z) = f z := by
    intro j
    induction j
    ·
      intro z _
      simp
    ·
      rename_i j ih
      intro z hz
      have hmem : ω ^ j * z ∈ Metric.ball (0 : ℂ) r := by
        rw [mem_ball_zero_iff] at hz ⊢
        simpa [norm_mul, norm_pow, hω1] using hz
      rw [pow_succ', mul_assoc, hinv _ hmem, ih z hz]
  have hroots : ∀ a b : ℂ, b ≠ 0 → a ^ e = b ^ e → ∃ j : ℕ, a = ω ^ j * b := by
    intro a b hb hab
    have h1 : (a / b) ^ e = 1 := by
      rw [div_pow, hab, div_self (pow_ne_zero _ hb)]
    obtain ⟨j, -, hj⟩ := hω.eq_pow_of_pow_eq_one h1
    exact ⟨j, by rw [hj, div_mul_cancel₀ _ hb]⟩
  have hnorm : ∀ z : ℂ, ‖z‖ < r ↔ ‖z ^ e‖ < r ^ e := fun z => by
    rw [norm_pow]
    apply (pow_lt_pow_iff_left₀ (norm_nonneg _) hr.le he0).symm
  have hex : ∀ w : ℂ, ∃ z : ℂ, z ^ e = w := fun w => IsAlgClosed.exists_pow_nat_eq w he
  choose root hroot using hex
  have hroot0 : root 0 = 0 := by
    simpa [he0] using hroot 0
  set F : ℂ → ℂ := fun w => f (root w) with hF
  have hFroot : ∀ z ∈ Metric.ball (0 : ℂ) r, F (z ^ e) = f z := by
    intro z hz
    obtain rfl | hz0 := eq_or_ne z 0
    · simp [hF, zero_pow he0, hroot0]
    ·
      obtain ⟨j, hj⟩ := hroots (root (z ^ e)) z hz0 (hroot _)
      simp only [hF]
      rw [hj, hinvj j z hz]
  refine ⟨F, fun w₀ hw₀ => ?_, fun z hz => (hFroot z hz).symm⟩
  have hAt : ∀ w₀ ∈ Metric.ball (0 : ℂ) (r ^ e), w₀ ≠ 0 → AnalyticAt ℂ F w₀ := by
    intro w₀ hw₀ hw₀0
    set z₀ := root w₀ with hz₀
    have hz₀e : z₀ ^ e = w₀ := hroot w₀
    have hz₀0 : z₀ ≠ 0 := by
      rintro h0
      rw [h0, zero_pow he0] at hz₀e
      apply hw₀0 hz₀e.symm
    set ρ : ℂ → ℂ := fun w => z₀ * Complex.exp (Complex.log (w / w₀) / e) with hρ
    have hρan : AnalyticAt ℂ ρ w₀ := by
      have h1 : AnalyticAt ℂ Complex.log (w₀ / w₀) := by
        rw [div_self hw₀0]
        apply analyticAt_clog Complex.one_mem_slitPlane
      have h2 : AnalyticAt ℂ (fun w : ℂ => w / w₀) w₀ := analyticAt_id.div_const
      apply analyticAt_const.mul _
      apply ((AnalyticAt.comp (f := fun w : ℂ => w / w₀) h1 h2).div_const (c := (e : ℂ))).cexp
    have hρe : ∀ w, w ≠ 0 → ρ w ^ e = w := by
      intro w hw
      simp only [hρ]
      rw [mul_pow, hz₀e, ← Complex.exp_nat_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 he0), Complex.exp_log (div_ne_zero hw hw₀0), mul_div_cancel₀ _ hw₀0]
    have hρball : ∀ w ∈ Metric.ball (0 : ℂ) (r ^ e), w ≠ 0 → ρ w ∈ Metric.ball (0 : ℂ) r := by
      intro w hw hw0
      rw [mem_ball_zero_iff] at hw ⊢
      rw [hnorm, hρe w hw0]
      apply hw
    apply ((hf (ρ w₀) (hρball w₀ hw₀ hw₀0)).comp hρan).congr _
    filter_upwards [Metric.isOpen_ball.mem_nhds hw₀, isOpen_ne.mem_nhds hw₀0] with w hwb hw0
    have hρw0 : ρ w ≠ 0 := by
      intro h0
      have := hρe w hw0
      rw [h0, zero_pow he0] at this
      apply hw0 this.symm
    obtain ⟨j, hj⟩ := hroots (root w) (ρ w) hρw0 (by rw [hroot, hρe w hw0])
    simp only [Function.comp_apply, hF]
    rw [hj, hinvj j (ρ w) (hρball w hwb hw0)]
  obtain rfl | hw₀0 := eq_or_ne w₀ 0
  ·
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    ·
      filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hw₀), self_mem_nhdsWithin] with w hwb hw0
      apply (hAt w hwb hw0).differentiableAt
    ·
      rw [Metric.continuousAt_iff]
      intro ε hε
      obtain ⟨δ, hδ, hfδ⟩ := Iff.mp Metric.continuousAt_iff (hf 0 (Metric.mem_ball_self hr)).continuousAt ε hε
      refine ⟨δ ^ e, pow_pos hδ e, fun w hw => ?_⟩
      simp only [hF, hroot0]
      apply hfδ
      rw [dist_zero_right] at hw ⊢
      rw [← hroot w, norm_pow] at hw
      apply lt_of_pow_lt_pow_left₀ e hδ.le hw
  · apply hAt w₀ hw₀ hw₀0


-- created on 2026-10-21
