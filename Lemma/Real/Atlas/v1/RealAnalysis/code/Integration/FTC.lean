import Mathlib
import sympy.Basic
open MeasureTheory Set Filter Topology intervalIntegral


namespace Integration

/--
[fundamental_theorem_of_calculus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/FTC.lean)
-/
@[path]
lemma fundamental_theorem_of_calculus
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a ≤ b)
  (hf : ContinuousOn f (Set.Icc a b)) :
-- imply
  (∀ F : ℝ → ℝ, (∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x) → ∫ x in a..b, f x = F b - F a) ∧ (∀ x ∈ Set.Icc a b, HasDerivWithinAt (fun t => ∫ u in a..t, f u) (f x) (Set.Icc a b) x) := by
-- proof
  have hrest : Continuous (Set.restrict (Set.Icc a b) f) := hf.restrict
  let fmap : C(↥(Set.Icc a b), ℝ) := ⟨Set.restrict (Set.Icc a b) f, hrest⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq isClosed_Icc fmap
  have hgf : ∀ x ∈ Set.Icc a b, (g : ℝ → ℝ) x = f x := fun x hx =>
    congr_fun (congr_arg ContinuousMap.toFun hg) ⟨x, hx⟩
  have hg_cont : Continuous (g : ℝ → ℝ) := g.continuous
  refine ⟨fun F hF => ?_, fun x hx => ?_⟩
  ·
    have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (f x) x := by
      intro x hx'; rw [Set.uIcc_of_le hab] at hx'; exact hF x hx'
    exact integral_eq_sub_of_hasDerivAt hderiv (hf.intervalIntegrable_of_Icc hab)
  ·
    have hg_deriv : HasDerivAt (fun t => ∫ u in a..t, (g : ℝ → ℝ) u) ((g : ℝ → ℝ) x) x :=
      (hg_cont.integral_hasStrictDerivAt a x).hasDerivAt
    rw [hgf x hx] at hg_deriv
    have hg_within : HasDerivWithinAt (fun t => ∫ u in a..t, (g : ℝ → ℝ) u)
      (f x) (Set.Icc a b) x := hg_deriv.hasDerivWithinAt
    have hint_eq : ∀ t ∈ Set.Icc a b,
      (∫ u in a..t, f u) = (∫ u in a..t, (g : ℝ → ℝ) u) := by
      intro t ht
      apply intervalIntegral.integral_congr_ae
      apply ae_of_all
      intro u hu
      rw [Set.uIoc_of_le ht.1] at hu
      exact (hgf u ⟨le_of_lt hu.1, le_trans hu.2 ht.2⟩).symm
    apply hg_within.congr_of_eventuallyEq
    · apply Filter.eventually_of_mem self_mem_nhdsWithin
      intro t ht
      exact hint_eq t ht
    · exact hint_eq x hx

end Integration

namespace Integration

/--
[integration_by_parts](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/FTC.lean)
-/
@[path]
lemma integration_by_parts
  {f g : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a ≤ b)
  (hf : ContDiffOn ℝ 1 f (Set.Icc a b))
  (hg : ContDiffOn ℝ 1 g (Set.Icc a b)) :
-- imply
  ∫ x in a..b, deriv f x * g x = f b * g b - f a * g a - ∫ x in a..b, f x * deriv g x := by
-- proof
  obtain rfl | hab' := hab.eq_or_lt
  · simp
  have hab_le : a ≤ b := hab'.le
  have hf_diff : DifferentiableOn ℝ f (Set.Icc a b) :=
    hf.differentiableOn one_ne_zero
  have hg_diff : DifferentiableOn ℝ g (Set.Icc a b) :=
    hg.differentiableOn one_ne_zero
  have hf_cont : ContinuousOn f (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab_le]; exact hf.continuousOn
  have hg_cont : ContinuousOn g (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab_le]; exact hg.continuousOn
  have hf_deriv : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt f (deriv f x) x := by
    intro x hx
    rw [min_eq_left hab_le, max_eq_right hab_le] at hx
    exact (hf_diff.differentiableAt (Icc_mem_nhds hx.1 hx.2)).hasDerivAt
  have hg_deriv : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt g (deriv g x) x := by
    intro x hx
    rw [min_eq_left hab_le, max_eq_right hab_le] at hx
    exact (hg_diff.differentiableAt (Icc_mem_nhds hx.1 hx.2)).hasDerivAt
  have huniq : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab'
  have hf'_int : IntervalIntegrable (deriv f) volume a b := by
    apply (hf.continuousOn_derivWithin huniq le_rfl).intervalIntegrable_of_Icc hab_le |>.congr_ae
    rw [Set.uIoc_of_le hab_le]
    exact ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx =>
        derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)))
  have hg'_int : IntervalIntegrable (deriv g) volume a b := by
    apply (hg.continuousOn_derivWithin huniq le_rfl).intervalIntegrable_of_Icc hab_le |>.congr_ae
    rw [Set.uIoc_of_le hab_le]
    exact ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx =>
        derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)))
  have key := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hg_cont hf_cont hg_deriv hf_deriv
    hg'_int hf'_int
  simp_rw [mul_comm (g _) (deriv f _), mul_comm (g b) (f b), mul_comm (g a) (f a),
    mul_comm (deriv g _) (f _)] at key
  exact key

end Integration

namespace Integration

/--
[change_of_variables](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/FTC.lean)
-/
@[path]
lemma change_of_variables
  {f : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a ≤ b)
  (hφ : ContDiffOn ℝ 1 φ (Set.Icc a b))
  (hφ_pos : ∀ x ∈ Set.Icc a b, 0 < deriv φ x)
  (hf : ContinuousOn f (Set.Icc (φ a) (φ b))) :
-- imply
  ∫ u in (φ a)..(φ b), f u = ∫ x in a..b, f (φ x) * deriv φ x := by
-- proof
  obtain rfl | hab_lt := hab.eq_or_lt
  · simp
  have hφ_diff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ φ x := fun x hx =>
    differentiableAt_of_deriv_ne_zero (hφ_pos x hx).ne'
  have hφ_hasderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt φ (deriv φ x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab_lt.le] at hx
    exact (hφ_diff x hx).hasDerivAt
  have hφ_deriv_cont : ContinuousOn (deriv φ) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab_lt.le]
    have huniq : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab_lt
    have hcont_dw := hφ.continuousOn_derivWithin huniq (le_refl 1)
    exact hcont_dw.congr (fun x hx => ((hφ_diff x hx).derivWithin (huniq x hx)).symm)
  have hφ_mono : StrictMonoOn φ (Set.Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) hφ.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    exact hφ_pos x (Ioo_subset_Icc_self hx)
  have hf_img : ContinuousOn f (φ '' Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab_lt.le]
    apply hf.mono
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨hφ_mono.monotoneOn (left_mem_Icc.mpr hab_lt.le) hx hx.1,
      hφ_mono.monotoneOn hx (right_mem_Icc.mpr hab_lt.le) hx.2⟩
  exact (integral_comp_mul_deriv' hφ_hasderiv hφ_deriv_cont hf_img).symm

end Integration


-- created on 2026-10-23
