import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.ComplexVariables.code.Lecture14
open Complex MeasureTheory Metric Set Filter Topology Classical in


/--
[residue_eq_of_differentiableOn_annulus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean)
-/
@[path]
lemma residue_eq_of_differentiableOn_annulus
  {a : ℂ}
  {r R : ℝ}
  {f : ℂ → ℂ}
  {s : Set ℂ}
-- given
  (hr : 0 < r)
  (hle : r ≤ R)
  (hs : s.Countable)
  (hc : ContinuousOn f (closedBall a R \ ball a r))
  (hd : ∀ z ∈ (ball a R \ closedBall a r) \ s, DifferentiableAt ℂ f z) :
-- imply
  residue f a R = residue f a r := by
-- proof
  unfold residue
  congr 1
  exact circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hle hs hc hd

/--
[residue_eq_of_differentiableOn_annulus'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean)
-/
@[path]
lemma residue_eq_of_differentiableOn_annulus'
  {a : ℂ}
  {r R : ℝ}
  {f : ℂ → ℂ}
-- given
  (hr : 0 < r)
  (hle : r ≤ R)
  (hc : ContinuousOn f (closedBall a R \ ball a r))
  (hd : ∀ z ∈ ball a R \ closedBall a r, DifferentiableAt ℂ f z) :
-- imply
  residue f a R = residue f a r :=
-- proof
  residue_eq_of_differentiableOn_annulus hr hle (s := ∅) countable_empty hc
    (fun z hz => hd z hz.1)

/--
[circleIntegral.integral_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean)
-/
@[path]
lemma circleIntegral.integral_neg
  {f : ℂ → ℂ}
  {c : ℂ}
  {R : ℝ} :
-- imply
  (∮ z in C(c, R), -f z) = -(∮ z in C(c, R), f z) := by
-- proof
  simp only [circleIntegral, smul_neg, intervalIntegral.integral_neg]
set_option maxHeartbeats 3200000 in

/--
[principal_part_integral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean)
-/
@[path]
lemma principal_part_integral_eq
  {c : ℂ}
  {R : ℝ}
  {a₀ : ℂ}
  {r₀ : ℝ}
  {f : ℂ → ℂ}
-- given
  (hR : 0 < R)
  (_ha₀ : a₀ ∈ ball c R)
  (hr₀ : 0 < r₀)
  (hrd₀ : closedBall a₀ r₀ ⊆ ball c R)
  (hf_cont : ContinuousOn f (sphere a₀ r₀)) :
-- imply
  ∮ z in C(c, R), ((2 * ↑Real.pi * I)⁻¹ * ∮ w in C(a₀, r₀), (w - z)⁻¹ * f w) = -∮ w in C(a₀, r₀), f w := by
-- proof
  have hconv : ∀ z, (2 * ↑Real.pi * I)⁻¹ * ∮ w in C(a₀, r₀), (w - z)⁻¹ * f w =
    -((2 * ↑Real.pi * I)⁻¹ * ∮ w in C(a₀, r₀), (z - w)⁻¹ * f w) := by
    intro z
    have : (fun w => (w - z)⁻¹ * f w) = (fun w => -((z - w)⁻¹ * f w)) := by
      ext w; rw [show w - z = -(z - w) from by ring, inv_neg, neg_mul]
    rw [this, circleIntegral.integral_neg, mul_neg]
  simp_rw [hconv]
  rw [circleIntegral.integral_neg]
  congr 1
  have hsph_ball : ∀ w ∈ sphere a₀ r₀, w ∈ ball c R :=
    fun w hw => hrd₀ (sphere_subset_closedBall hw)
  have hne : ∀ w ∈ sphere a₀ r₀, ∀ z ∈ sphere c R, z ≠ w := by
    intro w hw z hz hzw; rw [hzw] at hz
    have := hsph_ball w hw; rw [mem_ball] at this; rw [mem_sphere] at hz; linarith
  simp_rw [show ∀ z, (2 * ↑Real.pi * I)⁻¹ * ∮ w in C(a₀, r₀), (z - w)⁻¹ * f w =
    (2 * ↑Real.pi * I)⁻¹ • (∮ w in C(a₀, r₀), (z - w)⁻¹ * f w) from
    fun z => (smul_eq_mul _ _).symm]
  rw [circleIntegral.integral_smul, smul_eq_mul]
  suffices h_swap :
    ∮ z in C(c, R), ∮ w in C(a₀, r₀), (z - w)⁻¹ * f w =
    ∮ w in C(a₀, r₀), ∮ z in C(c, R), (z - w)⁻¹ * f w by
    rw [h_swap]
    simp_rw [show ∀ z w : ℂ, (z - w)⁻¹ * f w = f w * (z - w)⁻¹ from fun z w => mul_comm _ _]
    simp_rw [show ∀ w : ℂ, (fun z => f w * (z - w)⁻¹) = (fun z => f w • (z - w)⁻¹) from
      fun w => by ext z; rw [smul_eq_mul]]
    simp_rw [circleIntegral.integral_smul, smul_eq_mul]
    rw [circleIntegral.integral_congr hr₀.le (fun w hw => by
      rw [circleIntegral.integral_sub_inv_of_mem_ball (hsph_ball w hw)])]
    simp_rw [show ∀ w : ℂ, f w * (2 * ↑Real.pi * I) = (2 * ↑Real.pi * I) • f w from
      fun w => by rw [mul_comm, smul_eq_mul]]
    rw [circleIntegral.integral_smul, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  simp only [circleIntegral]
  simp_rw [← intervalIntegral.integral_smul]
  simp_rw [show ∀ (x y z : ℂ), x • (y • z) = y • (x • z) from fun x y z => by
    simp only [smul_eq_mul]; ring]
  have hle : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  simp_rw [intervalIntegral.integral_of_le hle]
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  apply IntegrableOn.mono_set ?_ (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  simp_rw [deriv_circleMap, smul_eq_mul]
  have hf_comp : ContinuousOn (f ∘ circleMap a₀ r₀) (Icc 0 (2 * Real.pi)) := by
    apply hf_cont.comp (continuous_circleMap a₀ r₀).continuousOn
    intro t _; exact circleMap_mem_sphere a₀ hr₀.le t
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · exact ((continuous_circleMap 0 R).continuousOn.comp continuousOn_fst (mapsTo_univ _ _))
    · exact continuousOn_const
  · apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact ((continuous_circleMap 0 r₀).continuousOn.comp continuousOn_snd (mapsTo_univ _ _))
      · exact continuousOn_const
    · apply ContinuousOn.mul
      · apply ContinuousOn.inv₀
        · exact ((continuous_circleMap c R).continuousOn.comp continuousOn_fst
          (mapsTo_univ _ _)).sub
          ((continuous_circleMap a₀ r₀).continuousOn.comp continuousOn_snd (mapsTo_univ _ _))
        · intro ⟨s, t⟩ ⟨hs, ht⟩
          simp only at hs ht
          exact sub_ne_zero.mpr (hne (circleMap a₀ r₀ t) (circleMap_mem_sphere a₀ hr₀.le t)
            (circleMap c R s) (circleMap_mem_sphere c hR.le s))
      · exact hf_comp.comp continuousOn_snd (fun ⟨_, t⟩ ⟨_, ht⟩ => ht)

/--
[logDeriv_sub_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean)
-/
@[path]
lemma logDeriv_sub_zpow
  {b : ℂ}
  {n : ℤ}
  {z : ℂ}
-- given
  (hz : z ≠ b) :
-- imply
  logDeriv (fun x => (x - b) ^ n) z = n / (z - b) := by
-- proof
  have hzb : z - b ≠ 0 := sub_ne_zero.mpr hz
  have : (fun x => (x - b) ^ n) = (fun x => x ^ n) ∘ (fun x => x - b) := by ext; simp
  rw [this, logDeriv_comp]
  · simp [logDeriv_zpow]
  · exact differentiableAt_zpow.mpr (Or.inl hzb)
  · exact differentiableAt_id.sub (differentiableAt_const b)

/--
[logDeriv_zero_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean)
-/
@[path]
lemma logDeriv_zero_decomposition
  {a : ℂ}
  {ε : ℝ}
  {f : ℂ → ℂ}
  {n : ℕ}
  {g : ℂ → ℂ}
-- given
  (hε : 0 < ε)
  (hg_hol : ∀ z ∈ closedBall a ε, DifferentiableAt ℂ g z)
  (hg_ne : ∀ z ∈ sphere a ε, g z ≠ 0)
  (hf_nhds : ∀ z ∈ sphere a ε, ∀ᶠ w in 𝓝 z, f w = (w - a) ^ n * g w) :
-- imply
  EqOn (logDeriv f) (fun z => (n : ℂ) / (z - a) + logDeriv g z) (sphere a ε) := by
-- proof
  intro z hz
  have hza : z ≠ a := ne_of_mem_sphere hz hε.ne'
  have hfe : f =ᶠ[𝓝 z] fun w => (w - a) ^ n * g w := hf_nhds z hz
  have hlf : logDeriv f z = logDeriv (fun w => (w - a) ^ n * g w) z := by
    unfold logDeriv; simp only [Pi.div_apply]; rw [hfe.deriv_eq, hfe.eq_of_nhds]
  rw [hlf]
  have hg_diff : DifferentiableAt ℂ g z := hg_hol z (sphere_subset_closedBall hz)
  have hg_nez : g z ≠ 0 := hg_ne z hz
  have hpow_diff : DifferentiableAt ℂ (fun w => (w - a) ^ n) z :=
    (differentiableAt_id.sub (differentiableAt_const a)).pow n
  have hpow_ne : (z - a) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hza)
  have key := logDeriv_mul (f := fun w => (w - a) ^ n) (g := g) z hpow_ne hg_nez hpow_diff hg_diff
  rw [key]
  congr 1
  have heq : (fun w : ℂ => (w - a) ^ n) = (fun w => (w - a) ^ (n : ℤ)) := by
    ext w; simp [zpow_natCast]
  rw [heq, logDeriv_sub_zpow a (n : ℤ) z hza]; simp

/--
[logDeriv_pole_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean)
-/
@[path]
lemma logDeriv_pole_decomposition
  {b : ℂ}
  {ε : ℝ}
  {f : ℂ → ℂ}
  {k : ℕ}
  {g : ℂ → ℂ}
-- given
  (hε : 0 < ε)
  (hg_hol : ∀ z ∈ closedBall b ε, DifferentiableAt ℂ g z)
  (hg_ne : ∀ z ∈ sphere b ε, g z ≠ 0)
  (hf_eq : ∀ z ∈ sphere b ε, ∀ᶠ w in 𝓝 z, f w = ((w - b) ^ k)⁻¹ * g w) :
-- imply
  EqOn (logDeriv f) (fun z => -(k : ℂ) / (z - b) + logDeriv g z) (sphere b ε) := by
-- proof
  intro z hz
  have hzb : z ≠ b := by
    intro h; rw [h] at hz; simp at hz; linarith
  have hfe : f =ᶠ[𝓝 z] fun w => ((w - b) ^ k)⁻¹ * g w := hf_eq z hz
  have hlf : logDeriv f z = logDeriv (fun w => ((w - b) ^ k)⁻¹ * g w) z := by
    unfold logDeriv
    simp only [Pi.div_apply]
    rw [hfe.deriv_eq, hfe.eq_of_nhds]
  rw [hlf]
  have hg_diff : DifferentiableAt ℂ g z := hg_hol z (sphere_subset_closedBall hz)
  have hg_nez : g z ≠ 0 := hg_ne z hz
  have hpow_diff : DifferentiableAt ℂ (fun w => ((w - b) ^ k)⁻¹) z := by
    apply DifferentiableAt.inv
    · exact (differentiableAt_id.sub (differentiableAt_const b)).pow k
    · exact pow_ne_zero k (sub_ne_zero.mpr hzb)
  have hpow_ne : ((z - b) ^ k)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero k (sub_ne_zero.mpr hzb))
  rw [logDeriv_mul z hpow_ne hg_nez hpow_diff hg_diff]
  congr 1
  have heq : (fun w : ℂ => ((w - b) ^ k)⁻¹) = (fun w => (w - b) ^ (-(k : ℤ))) := by
    ext w; simp [zpow_neg, zpow_natCast]
  rw [heq, logDeriv_sub_zpow b (-(k : ℤ)) z hzb]
  push_cast; ring

/--
[circleIntegral_logDeriv_eq_zero_of_image_in_unit_ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean)
-/
@[path]
lemma circleIntegral_logDeriv_eq_zero_of_image_in_unit_ball
  {c : ℂ}
  {R : ℝ}
  {ψ : ℂ → ℂ}
-- given
  (hR : 0 < R)
  (hψ_diff : ∀ z ∈ sphere c R, DifferentiableAt ℂ ψ z)
  (_hψ_cont : ContinuousOn ψ (sphere c R))
  (hψ_bound : ∀ z ∈ sphere c R, ‖ψ z - 1‖ < 1) :
-- imply
  ∮ z in C(c, R), logDeriv ψ z = 0 := by
-- proof
  have hψ_slit : ∀ z ∈ sphere c R, ψ z ∈ slitPlane := fun z hz => by
    have h := hψ_bound z hz
    have : ψ z = 1 + (ψ z - 1) := by ring
    rw [this]; exact mem_slitPlane_of_norm_lt_one h
  exact circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR.le fun z hz => by
    have heq : deriv (log ∘ ψ) z = logDeriv ψ z :=
      Complex.deriv_log_comp_eq_logDeriv (hψ_diff z hz) (hψ_slit z hz)
    rw [← heq]
    exact ((hψ_diff z hz).clog (hψ_slit z hz)).hasDerivAt.hasDerivWithinAt

/--
[rouche_integral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean)
-/
@[path]
lemma rouche_integral_eq
  {c : ℂ}
  {R : ℝ}
  {f g : ℂ → ℂ}
-- given
  (hR : 0 < R)
  (hf_diff : ∀ z ∈ closedBall c R, DifferentiableAt ℂ f z)
  (hg_diff : ∀ z ∈ closedBall c R, DifferentiableAt ℂ g z)
  (hbound : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖)
  (hf_int : CircleIntegrable (logDeriv f) c R)
  (hg_int : CircleIntegrable (logDeriv g) c R) :
-- imply
  (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv g z) = (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv f z) := by
-- proof
  congr 1
  have hf_ne : ∀ z ∈ sphere c R, f z ≠ 0 := by
    intro z hz hfz; have := hbound z hz; rw [hfz, norm_zero] at this
    exact not_lt.mpr (norm_nonneg _) this
  have hg_ne : ∀ z ∈ sphere c R, g z ≠ 0 := by
    intro z hz hgz; have := hbound z hz; rw [hgz, sub_zero] at this; exact lt_irrefl _ this
  have hψ_bound : ∀ z ∈ sphere c R, ‖g z / f z - 1‖ < 1 := by
    intro z hz
    have hfz := hf_ne z hz
    rw [div_sub_one hfz, norm_div, div_lt_one (norm_pos_iff.mpr hfz), norm_sub_rev]
    exact hbound z hz
  have hsphere_sub : sphere c R ⊆ closedBall c R := sphere_subset_closedBall
  have hgf_diff : ∀ z ∈ sphere c R, DifferentiableAt ℂ (fun z => g z / f z) z :=
    fun z hz => (hg_diff z (hsphere_sub hz)).div (hf_diff z (hsphere_sub hz)) (hf_ne z hz)
  have hgf_cont : ContinuousOn (fun z => g z / f z) (sphere c R) :=
    fun z hz => (hgf_diff z hz).continuousAt.continuousWithinAt
  have h_zero :=
    circleIntegral_logDeriv_eq_zero_of_image_in_unit_ball hR hgf_diff hgf_cont hψ_bound
  have h_eq : EqOn (logDeriv (fun z => g z / f z))
    (fun z => logDeriv g z - logDeriv f z) (sphere c R) :=
    fun z hz => logDeriv_div z (hg_ne z hz) (hf_ne z hz)
      (hg_diff z (hsphere_sub hz)) (hf_diff z (hsphere_sub hz))
  rw [circleIntegral.integral_congr hR.le h_eq] at h_zero
  rw [circleIntegral.integral_sub hg_int hf_int] at h_zero
  exact sub_eq_zero.mp h_zero

/--
[analyticAt_of_mem_ball_of_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean)
-/
@[path]
lemma analyticAt_of_mem_ball_of_closedBall
  {c : ℂ}
  {R : ℝ}
  {f : ℂ → ℂ}
  {a : ℂ}
-- given
  (hf : ∀ z ∈ closedBall c R, DifferentiableAt ℂ f z)
  (ha : a ∈ ball c R) :
-- imply
  AnalyticAt ℂ f a :=
-- proof
  Complex.analyticAt_iff_eventually_differentiableAt.mpr
    (eventually_of_mem (isOpen_ball.mem_nhds ha) (fun w hw => hf w (ball_subset_closedBall hw)))

/--
[analyticOrderAt_ne_top_in_ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean)
-/
@[path]
lemma analyticOrderAt_ne_top_in_ball
  {c : ℂ}
  {R : ℝ}
  {f : ℂ → ℂ}
  {a : ℂ}
-- given
  (hR : 0 < R)
  (hf : ∀ z ∈ closedBall c R, DifferentiableAt ℂ f z)
  (hf_ne : ∀ z ∈ sphere c R, f z ≠ 0)
  (ha : a ∈ ball c R) :
-- imply
  analyticOrderAt f a ≠ ⊤ := by
-- proof
  have ⟨w, hw, hfw⟩ : ∃ w ∈ ball c R, f w ≠ 0 := by
    by_contra h_all; push Not at h_all
    have hcont : ContinuousOn f (closedBall c R) :=
      fun z hz => (hf z hz).continuousAt.continuousWithinAt
    obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ ∈ sphere c R := ⟨c + R, by simp [abs_of_pos hR]⟩
    apply hf_ne w₀ hw₀
    have hw₀_cl : w₀ ∈ closure (ball c R) := by
      rw [closure_ball c (ne_of_gt hR)]; exact sphere_subset_closedBall hw₀
    have hmaps : MapsTo f (ball c R) {(0 : ℂ)} := fun z hz => h_all z hz
    have hm := hmaps.closure_of_continuousOn (by rwa [closure_ball c (ne_of_gt hR)]) hw₀_cl
    rw [closure_singleton] at hm; exact hm
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    (fun z hz => analyticAt_of_mem_ball_of_closedBall hf hz)
    (Metric.isConnected_ball hR).isPreconnected hw ha
    (fun h => hfw (analyticOrderAt_eq_top.mp h).self_of_nhds)

/--
[factorization_on_ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean)
-/
@[path]
lemma factorization_on_ball
  {f : ℂ → ℂ}
  {a : ℂ}
-- given
  (ha : AnalyticAt ℂ f a)
  (h_ne_top : analyticOrderAt f a ≠ ⊤) :
-- imply
  ∃ g : ℂ → ℂ, ∃ ε : ℝ, 0 < ε ∧ g a ≠ 0 ∧ (∀ z, dist z a < ε → f z = (z - a) ^ analyticOrderNatAt f a * g z) ∧ (∀ z, dist z a < ε → g z ≠ 0) ∧ (∀ z, dist z a < ε → DifferentiableAt ℂ g z) := by
-- proof
  obtain ⟨g, hga, hgne, hfg⟩ := ha.analyticOrderAt_ne_top.mp h_ne_top
  obtain ⟨ε₁, hε₁, hfg_ball⟩ := Metric.eventually_nhds_iff.mp hfg
  obtain ⟨ε₂, hε₂, hg_ne_ball⟩ := Metric.eventually_nhds_iff.mp
    (hga.continuousAt.eventually_ne hgne)
  obtain ⟨p, hp⟩ := hga
  obtain ⟨ε₃, hε₃, hg_diff_ball⟩ := Metric.eventually_nhds_iff.mp hp.eventually_differentiableAt
  refine ⟨g, min ε₁ (min ε₂ ε₃), by positivity, hgne, ?_, ?_, ?_⟩
  · intro z hz
    have := hfg_ball (lt_of_lt_of_le hz (min_le_left _ _))
    simp only [smul_eq_mul] at this; exact this
  · intro z hz
    exact hg_ne_ball (lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _)))
  · intro z hz
    exact hg_diff_ball (lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _)))

/--
[rouche_integral_eq_of_differentiableOn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean)
-/
@[path]
lemma rouche_integral_eq_of_differentiableOn
  {c : ℂ}
  {R : ℝ}
  {f g : ℂ → ℂ}
-- given
  (hR : 0 < R)
  (hf : ∀ z ∈ closedBall c R, DifferentiableAt ℂ f z)
  (hg : ∀ z ∈ closedBall c R, DifferentiableAt ℂ g z)
  (hbound : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖)
  (hf_int : CircleIntegrable (logDeriv f) c R)
  (hg_int : CircleIntegrable (logDeriv g) c R) :
-- imply
  (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv g z) = (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv f z) :=
-- proof
  rouche_integral_eq hR hf hg hbound hf_int hg_int


-- created on 2026-10-23
