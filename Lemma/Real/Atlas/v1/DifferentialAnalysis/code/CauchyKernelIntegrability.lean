import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.CauchyKernelIntegrability
open Real Set MeasureTheory Metric CauchyKernel
open scoped ENNReal Real Topology


namespace CauchyKernel

/--
[norm_polar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CauchyKernelIntegrability.lean)
-/
@[path]
lemma norm_polar
  {r θ : ℝ}
-- given
  (hr : 0 < r) :
-- imply
  ‖(↑(r * Real.cos θ) + Complex.I * ↑(r * Real.sin θ) : ℂ)‖ = r := by
-- proof
  have hrw : (↑(r * Real.cos θ) + Complex.I * ↑(r * Real.sin θ) : ℂ) =
    ↑(r * Real.cos θ) + ↑(r * Real.sin θ) * Complex.I := by ring
  rw [hrw, Complex.norm_add_mul_I]
  have hsq : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hsq, Real.sqrt_sq hr.le]

end CauchyKernel

namespace CauchyKernel

/--
[norm_cauchyKernelBare_polarCoord_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CauchyKernelIntegrability.lean)
-/
@[path]
lemma norm_cauchyKernelBare_polarCoord_symm
  {r θ : ℝ}
-- given
  (hr : 0 < r) :
-- imply
  ‖cauchyKernelBare (polarCoord.symm (r, θ))‖ = r⁻¹ := by
-- proof
  simp only [polarCoord_symm_apply, cauchyKernelBare, norm_inv, norm_polar r θ hr]

end CauchyKernel

namespace CauchyKernel

/--
[polar_in_closedBall_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CauchyKernelIntegrability.lean)
-/
@[path]
lemma polar_in_closedBall_bound
  {r θ R : ℝ}
-- given
  (hr : 0 < r)
  (hmem : polarCoord.symm (r, θ) ∈ closedBall (0 : ℝ × ℝ) R) :
-- imply
  r ≤ R * Real.sqrt 2 := by
-- proof
  simp only [polarCoord_symm_apply, mem_closedBall, Prod.dist_eq, Prod.fst_zero, Prod.snd_zero,
    Real.dist_eq, sub_zero] at hmem
  have hcos := le_of_max_le_left hmem; have hsin := le_of_max_le_right hmem
  have hR : 0 ≤ R := le_trans (abs_nonneg _) hcos
  have h3 : r ^ 2 ≤ 2 * R ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_abs (r * Real.cos θ), sq_abs (r * Real.sin θ),
      sq_le_sq' (by linarith [abs_nonneg (r * Real.cos θ)]) hcos,
      sq_le_sq' (by linarith [abs_nonneg (r * Real.sin θ)]) hsin]
  calc r ≤ Real.sqrt (2 * R ^ 2) := by rw [← Real.sqrt_sq hr.le]; exact Real.sqrt_le_sqrt h3
    _ = R * Real.sqrt 2 := by
      rw [Real.sqrt_mul (by norm_num : (2 : ℝ) ≥ 0), Real.sqrt_sq hR]; ring
end
set_option maxHeartbeats 800000 in


/--
[integrableOn_cauchyKernelBare_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CauchyKernelIntegrability.lean)
-/
@[path]
lemma integrableOn_cauchyKernelBare_closedBall
  {R : ℝ}
-- given
  (hR : 0 < R) :
-- imply
  IntegrableOn cauchyKernelBare (closedBall (0 : ℝ × ℝ) R) := by
-- proof
  constructor
  ·
    apply AEStronglyMeasurable.restrict
    exact (Measurable.inv (Measurable.add
      (measurable_fst.complex_ofReal)
      (Measurable.mul measurable_const measurable_snd.complex_ofReal))).aestronglyMeasurable
  ·
    show ∫⁻ p in closedBall (0 : ℝ × ℝ) R, ‖cauchyKernelBare p‖ₑ < ⊤
    simp_rw [enorm_eq_nnnorm]
    conv_lhs =>
      rw [← lintegral_indicator measurableSet_closedBall
        (fun p => (‖cauchyKernelBare p‖₊ : ℝ≥0∞)),
        ← lintegral_comp_polarCoord_symm]
    set F := fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
      (closedBall (0 : ℝ × ℝ) R).indicator
        (fun p => (‖cauchyKernelBare p‖₊ : ℝ≥0∞)) (polarCoord.symm p)
    set S : Set (ℝ × ℝ) := Set.Ioc 0 (R * Real.sqrt 2) ×ˢ Set.Ioo (-Real.pi) Real.pi
      with hS_def
    have hSmeas : MeasurableSet S := measurableSet_Ioc.prod measurableSet_Ioo
    have hSvol : volume S < ⊤ := by
      rw [hS_def, Measure.volume_eq_prod, Measure.prod_prod,
        Real.volume_Ioc, Real.volume_Ioo]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    have hpw : ∀ p ∈ polarCoord.target,
      F p ≤ S.indicator (fun _ => (1 : ℝ≥0∞)) p := by
      intro ⟨r, θ⟩ hp
      rw [polarCoord_target] at hp; obtain ⟨hr, hθ⟩ := hp
      simp only [F]
      by_cases hmem : polarCoord.symm (r, θ) ∈ closedBall (0 : ℝ × ℝ) R
      · rw [Set.indicator_of_mem hmem]
        have hr_pos : 0 < r := Set.mem_Ioi.mp hr
        have hnorm : (‖cauchyKernelBare (polarCoord.symm (r, θ))‖₊ : ℝ≥0∞) =
          ENNReal.ofReal r⁻¹ := by
          rw [ENNReal.ofReal]; congr 1; ext
          simp only [coe_nnnorm, norm_cauchyKernelBare_polarCoord_symm hr_pos,
            Real.coe_toNNReal _ (inv_nonneg.mpr hr_pos.le)]
        rw [hnorm, show ENNReal.ofReal r • ENNReal.ofReal r⁻¹ = (1 : ℝ≥0∞) from by
          simp only [smul_eq_mul]
          rw [← ENNReal.ofReal_mul hr_pos.le, mul_inv_cancel₀ hr_pos.ne',
            ENNReal.ofReal_one]]
        rw [Set.indicator_of_mem (show (r, θ) ∈ S from
          ⟨⟨hr_pos, polar_in_closedBall_bound hr_pos hmem⟩, hθ⟩)]
      · rw [Set.indicator_of_notMem hmem, smul_zero]; exact zero_le _
    calc ∫⁻ p in polarCoord.target, F p
      ≤ ∫⁻ p in polarCoord.target, S.indicator (fun _ => 1) p :=
        setLIntegral_mono (by measurability) (fun p hp => hpw p hp)
      _ ≤ ∫⁻ p, S.indicator (fun _ => 1) p := setLIntegral_le_lintegral _ _
      _ = volume S := by
        rw [lintegral_indicator hSmeas]
        simp only [lintegral_one, Measure.restrict_apply_univ]
      _ < ⊤ := hSvol
noncomputable section

/--
[cauchyKernelBare_locallyIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CauchyKernelIntegrability.lean)
-/
@[path]
lemma cauchyKernelBare_locallyIntegrable
-- imply
  LocallyIntegrable cauchyKernelBare := by
-- proof
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 0
  exact (integrableOn_cauchyKernelBare_closedBall R hR).mono_set hKR
end


-- created on 2026-10-23
