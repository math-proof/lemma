import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private noncomputable def zmap (p : ℝ × ℝ) : ℂ :=
  ((p.1 / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (p.2 : ℝ)

private noncomputable def Φ : ℂ → ℂ :=
  dslope Complex.exp 0

private noncomputable def γ (p : ℝ × ℝ) : ℝ :=
  ‖(1 : ℂ) - Complex.exp (zmap p)‖ ^ 2 * Real.log ‖(1 : ℂ) - Complex.exp (zmap p)‖

private noncomputable def acoef (p : ℝ × ℝ) : ℝ :=
  ‖Φ (zmap p)‖ ^ 2 / 2

private noncomputable def bcoef (p : ℝ × ℝ) : ℝ :=
  ‖Φ (zmap p)‖ ^ 2 * (Real.log (‖Φ (zmap p)‖ ^ 2) / 2)

private lemma mul_Φ (z : ℂ) :
  -- imply
  z * Φ z = Complex.exp z - 1 := by
  -- proof
  simpa [Φ, smul_eq_mul] using sub_smul_dslope Complex.exp 0 z

private lemma one_sub_exp_eq (z : ℂ) :
  -- imply
  (1 : ℂ) - Complex.exp z = -(z * Φ z) := by
  -- proof
  rw [mul_Φ]
  ring

private lemma differentiable_Φ :
  -- imply
  Differentiable ℂ Φ := by
  -- proof
  apply Iff.mp differentiableOn_univ
  apply Iff.mpr (Complex.differentiableOn_dslope Filter.univ_mem)
  apply Complex.differentiable_exp.differentiableOn

private lemma contDiff_Φ :
  -- imply
  ContDiff ℝ (⊤ : ENat) Φ := by
  -- proof
  apply ((differentiable_Φ).contDiff (n := ((⊤ : ENat) : WithTop ENat))).restrict_scalars ℝ

private lemma Φ_zero :
  -- imply
  Φ 0 = 1 := by
  -- proof
  simp [Φ, dslope_same]

private lemma contDiff_zmap :
  -- imply
  ContDiff ℝ (⊤ : ENat) zmap := by
  -- proof
  unfold zmap
  apply ContDiff.add
  · apply Complex.ofRealCLM.contDiff.comp ((contDiff_fst).div_const 2)
  · apply contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd)

private lemma zmap_re (p : ℝ × ℝ) :
  -- imply
  (zmap p).re = p.1 / 2 := by
  -- proof
  simp [zmap]

private lemma zmap_im (p : ℝ × ℝ) :
  -- imply
  (zmap p).im = 2 * Real.pi * p.2 := by
  -- proof
  simp [zmap]

private lemma normSq_zmap (p : ℝ × ℝ) :
  -- imply
  ‖zmap p‖ ^ 2 = p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2 := by
  -- proof
  rw [Complex.sq_norm, Complex.normSq_apply, zmap_re, zmap_im]
  ring

private lemma exp_zmap_eq_one_iff (p : ℝ × ℝ) :
  -- imply
  Complex.exp (zmap p) = 1 ↔ p.1 = 0 ∧ ∃ k : ℤ, p.2 = k := by
  -- proof
  constructor
  ·
    intro h
    obtain ⟨n, hn⟩ := Iff.mp Complex.exp_eq_one_iff h
    have hre := congrArg Complex.re hn
    have him := congrArg Complex.im hn
    rw [zmap_re] at hre
    rw [zmap_im] at him
    simp at hre him
    refine ⟨by linarith, n, ?_⟩
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    have : 2 * Real.pi * p.2 = 2 * Real.pi * n := by linarith
    apply mul_left_cancel₀ (by positivity) this
  ·
    rintro ⟨h1, k, hk⟩
    have : zmap p = k * (2 * Real.pi * Complex.I) := by
      apply Complex.ext
      · simp [zmap_re, h1]
      ·
        simp [zmap_im, hk]
        ring
    rw [this]
    apply Iff.mpr Complex.exp_eq_one_iff ⟨k, rfl⟩

private lemma Φ_zmap_ne_zero (p : ℝ × ℝ) (hp : |p.2| < 1 / 2) :
  -- imply
  Φ (zmap p) ≠ 0 := by
  -- proof
  intro h
  if hz : zmap p = 0 then
    rw [hz, Φ_zero] at h
    apply one_ne_zero h
  else
    have h1 : Complex.exp (zmap p) = 1 := by
      have := mul_Φ (zmap p)
      rw [h, mul_zero] at this
      apply Iff.mp sub_eq_zero this.symm
    obtain ⟨h0, k, hk⟩ := Iff.mp (exp_zmap_eq_one_iff p) h1
    rw [hk] at hp
    have hk0 : k = 0 := by
      have : |(k : ℝ)| < 1 := by linarith
      apply Int.abs_lt_one_iff.mp (by exact_mod_cast this)
    apply hz
    apply Complex.ext
    · simp [zmap_re, h0]
    · simp [zmap_im, hk, hk0]

private lemma zmap_eq_zero_iff (p : ℝ × ℝ) :
  -- imply
  zmap p = 0 ↔ p.1 = 0 ∧ p.2 = 0 := by
  -- proof
  constructor
  ·
    intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    rw [zmap_re] at hre
    rw [zmap_im] at him
    simp only [Complex.zero_re, Complex.zero_im] at hre him
    refine ⟨by linarith, ?_⟩
    have : 2 * Real.pi * p.2 = 2 * Real.pi * 0 := by
      rw [him]
      ring
    apply mul_left_cancel₀ (by positivity) this
  ·
    rintro ⟨h1, h2⟩
    apply Complex.ext
    · simp [zmap_re, h1]
    · simp [zmap_im, h2]

private lemma contDiff_acoef :
  -- imply
  ContDiff ℝ (⊤ : ENat) acoef := by
  -- proof
  unfold acoef
  apply ((contDiff_Φ.comp contDiff_zmap).norm_sq (𝕜 := ℂ)).div_const 2

private lemma contDiffOn_bcoef :
  -- imply
  ContDiffOn ℝ (⊤ : ENat) bcoef {p : ℝ × ℝ | |p.2| < 1 / 2} := by
  -- proof
  unfold bcoef
  have hn : ContDiff ℝ (⊤ : ENat) (fun p : ℝ × ℝ => ‖Φ (zmap p)‖ ^ 2) :=
    (contDiff_Φ.comp contDiff_zmap).norm_sq (𝕜 := ℂ)
  apply hn.contDiffOn.mul ((hn.contDiffOn.log _).div_const 2)
  intro p hp
  apply pow_ne_zero 2 (norm_ne_zero_iff.mpr (Φ_zmap_ne_zero p hp))

private lemma acoef_pos (p : ℝ × ℝ) (hp : |p.2| < 1 / 2) :
  -- imply
  0 < acoef p := by
  -- proof
  unfold acoef
  have : 0 < ‖Φ (zmap p)‖ := norm_pos_iff.mpr (Φ_zmap_ne_zero p hp)
  positivity

private lemma γ_eq (p : ℝ × ℝ) (hp : |p.2| < 1 / 2) :
  -- imply
  γ p = acoef p * ((p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2) *
      Real.log (p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2)) +
      (p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2) * bcoef p := by
  -- proof
  have hΦ : ‖Φ (zmap p)‖ ≠ 0 := norm_ne_zero_iff.mpr (Φ_zmap_ne_zero p hp)
  unfold γ acoef bcoef
  rw [← normSq_zmap, one_sub_exp_eq, norm_neg, norm_mul]
  set u : ℝ := ‖zmap p‖
  set v : ℝ := ‖Φ (zmap p)‖
  if hu0 : u = 0 then
    simp [hu0]
  else
    have hlogmul : Real.log (u * v) = Real.log u + Real.log v := Real.log_mul hu0 hΦ
    have hlogu2 : Real.log (u ^ 2) = 2 * Real.log u := by
      rw [Real.log_pow]
      norm_num
    have hlogv2 : Real.log (v ^ 2) = 2 * Real.log v := by
      rw [Real.log_pow]
      norm_num
    rw [hlogmul, hlogu2, hlogv2]
    ring

private lemma contDiffOn_γ :
  -- imply
  ContDiffOn ℝ (⊤ : ENat) γ {p : ℝ × ℝ | Complex.exp (zmap p) ≠ 1} := by
  -- proof
  have hw : ContDiff ℝ (⊤ : ENat) (fun p : ℝ × ℝ => (1 : ℂ) - Complex.exp (zmap p)) :=
    contDiff_const.sub ((Complex.contDiff_exp (𝕜 := ℝ)).comp contDiff_zmap)
  have hn : ContDiff ℝ (⊤ : ENat) (fun p : ℝ × ℝ => ‖(1 : ℂ) - Complex.exp (zmap p)‖ ^ 2) :=
    hw.norm_sq (𝕜 := ℂ)
  have hne : ∀ p ∈ {p : ℝ × ℝ | Complex.exp (zmap p) ≠ 1}, ‖(1 : ℂ) - Complex.exp (zmap p)‖ ^ 2 ≠ 0 := by
    intro p hp
    have : (1 : ℂ) - Complex.exp (zmap p) ≠ 0 := by
      intro h
      apply hp (Iff.mp sub_eq_zero h).symm
    positivity
  have hlog : ContDiffOn ℝ (⊤ : ENat)
    (fun p : ℝ × ℝ => Real.log (‖(1 : ℂ) - Complex.exp (zmap p)‖ ^ 2))
    {p : ℝ × ℝ | Complex.exp (zmap p) ≠ 1} := hn.contDiffOn.log hne
  have h : ContDiffOn ℝ (⊤ : ENat)
    (fun p : ℝ × ℝ => ‖(1 : ℂ) - Complex.exp (zmap p)‖ ^ 2 *
      (Real.log (‖(1 : ℂ) - Complex.exp (zmap p)‖ ^ 2) / 2))
    {p : ℝ × ℝ | Complex.exp (zmap p) ≠ 1} := hn.contDiffOn.mul (hlog.div_const 2)
  refine h.congr ?_
  intro p _
  unfold γ
  rw [Real.log_pow]
  push_cast
  ring

/--
[Complex_exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Complex_exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add.lean)
-/
@[path]
private lemma main :
  -- imply
  ∃ a b : ℝ × ℝ → ℝ, ContDiffOn ℝ (⊤ : ENat) a {p : ℝ × ℝ | |p.2| < 1 / 2} ∧
    ContDiffOn ℝ (⊤ : ENat) b {p : ℝ × ℝ | |p.2| < 1 / 2} ∧
    (∀ p : ℝ × ℝ, |p.2| < 1 / 2 → 0 < a p) ∧
    (∀ p : ℝ × ℝ, |p.2| < 1 / 2 →
      ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ ^ 2 *
          Real.log ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ =
        a p * ((p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2) *
            Real.log (p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2)) +
          (p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2) * b p) ∧
    (∀ p : ℝ × ℝ, Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ)) = 1 ↔
      p.1 = 0 ∧ ∃ k : ℤ, p.2 = k) ∧
    ContDiffOn ℝ (⊤ : ENat)
      (fun p : ℝ × ℝ =>
        ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ ^ 2 *
          Real.log ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖)
      {p : ℝ × ℝ | Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ)) ≠ 1} := by
  -- proof
  refine ⟨acoef, bcoef, contDiff_acoef.contDiffOn, contDiffOn_bcoef, acoef_pos, ?_, ?_, ?_⟩
  ·
    intro p hp
    apply γ_eq p hp
  ·
    intro p
    apply exp_zmap_eq_one_iff p
  · apply contDiffOn_γ


-- created on 2026-10-20
