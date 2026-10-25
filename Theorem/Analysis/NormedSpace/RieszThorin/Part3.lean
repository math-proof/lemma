/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Def.Analysis.NormedSpace.RieszThorin.Part2


section

open MeasureTheory

namespace FunctionalAnalysis.RieszThorinWanted

lemma ph_mul {α : Type*} (h : α → Complex) (i : α) :
    ph h i * (‖h i‖ : ℂ) = h i := by
  unfold ph
  by_cases hh : h i = 0
  · simp [hh]
  · rw [ite_eq_right hh, div_mul_cancel₀ _ (by exact_mod_cast
      (fun e => hh (norm_eq_zero.mp e)))]

lemma norm_ph {α : Type*} (h : α → Complex) (i : α) :
    ‖ph h i‖ = if h i = 0 then 0 else 1 := by
  unfold ph
  by_cases hh : h i = 0
  · simp [hh]
  · rw [ite_eq_right hh, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Complex.norm_nonneg _), ite_eq_right hh]
    exact div_self (fun e => hh (norm_eq_zero.mp e))

lemma fam_bound {α : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h : α → Complex) {r r₀ r₁ : ENNReal} {θ : ℝ}
    (hr0 : 1 ≤ r₀) (hr1 : 1 ≤ r₁)
    (hr_eq : r⁻¹ = ENNReal.ofReal (1 - θ) * r₀⁻¹ + ENNReal.ofReal θ * r₁⁻¹)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hnorm : eLpNorm h r Measure.count = 1) :
    ∃ H : ℂ → (α → Complex),
      H ((θ : ℝ) : ℂ) = h
      ∧ (∀ z : ℂ, z.re = 0 → eLpNorm (H z) r₀ Measure.count = 1)
      ∧ (∀ z : ℂ, z.re = 1 → eLpNorm (H z) r₁ Measure.count = 1)
      ∧ (∀ i, Differentiable ℂ (fun z => H z i))
      ∧ ∃ B : α → ℝ, ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1,
        ∀ i, ‖H z i‖ ≤ B i := by
  classical
  have := Fintype.ofFinite α
  have hr00 : r₀ ≠ 0 := ne_of_gt (one_pos.trans_le hr0)
  have hr10 : r₁ ≠ 0 := ne_of_gt (one_pos.trans_le hr1)
  have hrinvT : r⁻¹ ≠ ⊤ := by
    rw [hr_eq, ENNReal.add_ne_top]
    exact ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.mpr hr00),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.inv_ne_top.mpr hr10)⟩
  have hr_ne0 : r ≠ 0 := ENNReal.inv_ne_top.mp hrinvT
  have hhne : h ≠ 0 := by
    intro h0
    rw [h0, eLpNorm_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨i₁, hi₁⟩ : ∃ i, h i ≠ 0 := by
    by_contra hall
    apply hhne
    funext i
    by_contra hi
    exact hall ⟨i, hi⟩
  by_cases hinf : r₀ = ⊤ ∧ r₁ = ⊤
  · obtain ⟨rfl, rfl⟩ := hinf
    have hrT : r = ⊤ := by
      have h : r⁻¹ = 0 := by simpa using hr_eq
      exact ENNReal.inv_eq_zero.mp h
    refine ⟨fun _ => h, rfl, ?_, ?_, ?_, ?_⟩
    · intro z _
      change eLpNorm h _ _ = _
      rw [← hrT]
      exact hnorm
    · intro z _
      change eLpNorm h _ _ = _
      rw [← hrT]
      exact hnorm
    · intro i
      exact differentiable_const _
    · exact ⟨fun i => ‖h i‖, fun z _ i => le_rfl⟩
  · have hrT : r ≠ ⊤ := by
      by_cases h0T : r₀ = ⊤
      · have h1T : r₁ ≠ ⊤ := fun h => hinf ⟨h0T, h⟩
        have h1 : r₁⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr h1T
        have h2 : ENNReal.ofReal θ ≠ 0 := (ENNReal.ofReal_pos.mpr hθ₀).ne'
        have h3 : ENNReal.ofReal θ * r₁⁻¹ ≠ 0 := mul_ne_zero h2 h1
        intro hTT
        have h4 : ENNReal.ofReal θ * r₁⁻¹ ≤ r⁻¹ := by
          rw [hr_eq]; exact le_add_left le_rfl
        rw [hTT, show (⊤ : ENNReal)⁻¹ = 0 from by simp] at h4
        exact h3 (le_antisymm h4 zero_le)
      · have h1 : r₀⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr h0T
        have h2 : ENNReal.ofReal (1 - θ) ≠ 0 :=
          (ENNReal.ofReal_pos.mpr (sub_pos.mpr hθ₁)).ne'
        have h3 : ENNReal.ofReal (1 - θ) * r₀⁻¹ ≠ 0 := mul_ne_zero h2 h1
        intro hTT
        have h4 : ENNReal.ofReal (1 - θ) * r₀⁻¹ ≤ r⁻¹ := by
          rw [hr_eq]; exact le_add_right le_rfl
        rw [hTT, show (⊤ : ENNReal)⁻¹ = 0 from by simp] at h4
        exact h3 (le_antisymm h4 zero_le)
    have hP : 0 < r.toReal := ENNReal.toReal_pos hr_ne0 hrT
    set A : ℂ → ℂ := fun z =>
      (r.toReal : ℂ) * ((1 - z) * ((r₀⁻¹).toReal : ℂ) +
        z * ((r₁⁻¹).toReal : ℂ)) with hA
    set H : ℂ → (α → Complex) := fun z i =>
      if h i = 0 then 0 else ph h i *
        Complex.exp (A z * Real.log ‖h i‖) with hH
    have hmid : (r⁻¹).toReal =
        (1 - θ) * (r₀⁻¹).toReal + θ * (r₁⁻¹).toReal := by
      have h := congrArg ENNReal.toReal hr_eq
      rw [ENNReal.toReal_add
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.inv_ne_top.mpr hr00))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.inv_ne_top.mpr hr10)),
        ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hθ₁.le),
        ENNReal.toReal_ofReal hθ₀.le] at h
      exact h
    have hAre : ∀ z : ℂ, (A z).re = r.toReal *
        ((1 - z.re) * (r₀⁻¹).toReal + z.re * (r₁⁻¹).toReal) := by
      intro z
      rw [hA]
      change ((r.toReal : ℂ) * ((1 - z) * ((r₀⁻¹).toReal : ℂ) +
        z * ((r₁⁻¹).toReal : ℂ))).re = _
      simp only [Complex.mul_re, Complex.add_re, Complex.sub_re,
        Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
      ring
    have hAθ : A ((θ : ℝ) : ℂ) = 1 := by
      have hmid2 : r.toReal * ((1 - θ) * (r₀⁻¹).toReal +
          θ * (r₁⁻¹).toReal) = 1 := by
        rw [← hmid, ENNReal.toReal_inv, mul_inv_cancel₀ hP.ne']
      rw [hA]
      change ((r.toReal : ℂ) * ((1 - ↑θ) * ((r₀⁻¹).toReal : ℂ) +
        ↑θ * ((r₁⁻¹).toReal : ℂ)) : ℂ) = 1
      exact_mod_cast hmid2
    have hHnorm : ∀ z : ℂ, ∀ i : α, ‖H z i‖ =
        if h i = 0 then 0 else ‖h i‖ ^ (A z).re := by
      intro z i
      by_cases hh : h i = 0
      · have hHz : H z i = 0 := by
          rw [hH]
          change (if h i = 0 then (0 : ℂ) else _) = 0
          rw [ite_eq_left hh]
        rw [hHz, norm_zero, ite_eq_left hh]
      · have hpos : 0 < ‖h i‖ := norm_pos_iff.mpr hh
        rw [hH]
        change ‖(if h i = 0 then (0 : ℂ) else _)‖ = _
        rw [ite_eq_right hh, norm_mul, norm_ph, ite_eq_right hh, one_mul,
          Complex.norm_exp]
        have hre : (A z * ((Real.log ‖h i‖ : ℝ) : ℂ)).re =
            (A z).re * Real.log ‖h i‖ := by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            mul_zero, sub_zero]
        rw [hre, mul_comm, ← Real.rpow_def_of_pos hpos, ite_eq_right hh]
    have hSnn : 0 ≤ ∑ i, ‖h i‖ ^ r.toReal :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (Complex.norm_nonneg _) _
    have h1Pnn : (0 : ℝ) ≤ 1 / r.toReal := le_of_lt (one_div_pos.mpr hP)
    have hinner_h : (∑ i, ‖h i‖ₑ ^ r.toReal) =
        ENNReal.ofReal (∑ i, ‖h i‖ ^ r.toReal) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        Real.rpow_nonneg (Complex.norm_nonneg _) _)]
      apply Finset.sum_congr rfl; intro i _
      rw [enorm_complex_eq_ofReal,
        ENNReal.ofReal_rpow_of_nonneg (Complex.norm_nonneg _)
          ENNReal.toReal_nonneg]
    have hAeq_h : (eLpNorm h r Measure.count).toReal =
        (∑ i, ‖h i‖ ^ r.toReal) ^ (1 / r.toReal) := by
      rw [eLpNorm_count_eq_sum h hr_ne0 hrT, hinner_h,
        ENNReal.ofReal_rpow_of_nonneg hSnn h1Pnn,
        ENNReal.toReal_ofReal (Real.rpow_nonneg hSnn _)]
    have hSh : ∑ i, ‖h i‖ ^ r.toReal = 1 := by
      have h4 : ((∑ i, ‖h i‖ ^ r.toReal) ^ (1 / r.toReal)) ^ r.toReal
          = (∑ i, ‖h i‖ ^ r.toReal) := by
        rw [← Real.rpow_mul hSnn, div_mul_cancel₀ 1 hP.ne', Real.rpow_one]
      rw [← h4, ← hAeq_h, hnorm, ENNReal.toReal_one, Real.one_rpow]
    have hHθ : H ((θ : ℝ) : ℂ) = h := by
      funext i
      rw [hH]
      change (if h i = 0 then (0 : ℂ) else _) = _
      by_cases hh : h i = 0
      · rw [ite_eq_left hh, hh]
      · rw [ite_eq_right hh, hAθ, one_mul, ← Complex.ofReal_exp,
          Real.exp_log (norm_pos_iff.mpr hh)]
        exact ph_mul h i
    have bnd_top : ∀ z : ℂ, (A z).re = 0 →
        eLpNorm (H z) ⊤ Measure.count = 1 := by
      intro z hre0
      rw [eLpNorm_count_top_eq]
      apply le_antisymm
      · apply iSup_le; intro i
        rw [enorm_complex_eq_ofReal, hHnorm z i]
        by_cases hh : h i = 0
        · rw [ite_eq_left hh]; simp
        · rw [ite_eq_right hh, hre0, Real.rpow_zero]; simp
      · have h1l : ‖H z i₁‖ₑ = 1 := by
          rw [enorm_complex_eq_ofReal, hHnorm z i₁, ite_eq_right hi₁, hre0,
            Real.rpow_zero, ENNReal.ofReal_one]
        rw [← h1l]
        exact le_iSup (fun i => ‖H z i‖ₑ) i₁
    have bnd_fin : ∀ s : ENNReal, 1 ≤ s → ∀ z : ℂ,
        (A z).re * s.toReal = r.toReal →
        eLpNorm (H z) s Measure.count = 1 := by
      intro s hs z hre
      have hsT : s ≠ ⊤ := by
        rintro rfl
        rw [ENNReal.toReal_top, mul_zero] at hre
        exact hP.ne' hre.symm
      have hs0 : s ≠ 0 := ne_of_gt (one_pos.trans_le hs)
      have hRle : 1 ≤ s.toReal := by
        have h := (ENNReal.toReal_le_toReal (by simp : (1 : ENNReal) ≠ ⊤)
          hsT).mpr hs
        rwa [ENNReal.toReal_one] at h
      have hR : 0 < s.toReal := zero_lt_one.trans_le hRle
      have hpt : ∀ i, ‖H z i‖ ^ s.toReal = ‖h i‖ ^ r.toReal := by
        intro i
        rw [hHnorm z i]
        by_cases hh : h i = 0
        · rw [ite_eq_left hh]
          have hh0 : ‖h i‖ = 0 := norm_eq_zero.mpr hh
          rw [hh0, Real.zero_rpow (ne_of_gt hR), Real.zero_rpow hP.ne']
        · rw [ite_eq_right hh, ← Real.rpow_mul (Complex.norm_nonneg _), hre]
      have htm : ∀ i, ‖H z i‖ₑ ^ s.toReal =
          ENNReal.ofReal (‖h i‖ ^ r.toReal) := by
        intro i
        rw [enorm_complex_eq_ofReal,
          ENNReal.ofReal_rpow_of_nonneg (Complex.norm_nonneg _)
            ENNReal.toReal_nonneg,
          hpt i]
      have hsumH : (∑ i, ‖H z i‖ₑ ^ s.toReal) = 1 := by
        rw [Finset.sum_congr rfl (fun i _ => htm i),
          ← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
            Real.rpow_nonneg (Complex.norm_nonneg _) _),
          hSh, ENNReal.ofReal_one]
      rw [eLpNorm_count_eq_sum _ hs0 hsT, hsumH]
      simp
    have hre_z0 : ∀ z : ℂ, z.re = 0 → (A z).re =
        r.toReal * (r₀⁻¹).toReal := by
      intro z hz
      rw [hAre z, hz, sub_zero, one_mul, zero_mul, add_zero]
    have hre_z1 : ∀ z : ℂ, z.re = 1 → (A z).re =
        r.toReal * (r₁⁻¹).toReal := by
      intro z hz
      rw [hAre z, hz, sub_self, zero_mul, one_mul, zero_add]
    have bnd0 : ∀ z : ℂ, z.re = 0 → eLpNorm (H z) r₀ Measure.count = 1 := by
      intro z hz
      rcases eq_or_ne r₀ ⊤ with rfl | hr0T
      · have hre0 : (A z).re = 0 := by
          rw [hre_z0 z hz]
          simp
        exact bnd_top z hre0
      · have hR₀le : 1 ≤ r₀.toReal := by
          have h := (ENNReal.toReal_le_toReal (by simp : (1 : ENNReal) ≠ ⊤)
            hr0T).mpr hr0
          rwa [ENNReal.toReal_one] at h
        have hPR : (r₀⁻¹).toReal * r₀.toReal = 1 := by
          rw [ENNReal.toReal_inv,
            inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans_le hR₀le))]
        have hreP : (A z).re * r₀.toReal = r.toReal := by
          rw [hre_z0 z hz, mul_assoc, hPR, mul_one]
        exact bnd_fin r₀ hr0 z hreP
    have bnd1 : ∀ z : ℂ, z.re = 1 → eLpNorm (H z) r₁ Measure.count = 1 := by
      intro z hz
      rcases eq_or_ne r₁ ⊤ with rfl | hr1T
      · have hre1 : (A z).re = 0 := by
          rw [hre_z1 z hz]
          simp
        exact bnd_top z hre1
      · have hR₁le : 1 ≤ r₁.toReal := by
          have h := (ENNReal.toReal_le_toReal (by simp : (1 : ENNReal) ≠ ⊤)
            hr1T).mpr hr1
          rwa [ENNReal.toReal_one] at h
        have hPR : (r₁⁻¹).toReal * r₁.toReal = 1 := by
          rw [ENNReal.toReal_inv,
            inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans_le hR₁le))]
        have hreP : (A z).re * r₁.toReal = r.toReal := by
          rw [hre_z1 z hz, mul_assoc, hPR, mul_one]
        exact bnd_fin r₁ hr1 z hreP
    have hA_diff : Differentiable ℂ A := by
      rw [hA]
      show Differentiable ℂ (fun z : ℂ =>
        (r.toReal : ℂ) * ((1 - z) * ((r₀⁻¹).toReal : ℂ) +
          z * ((r₁⁻¹).toReal : ℂ)))
      exact (((differentiable_const _).sub differentiable_id).mul_const _).add
        (differentiable_id.mul_const _) |>.const_mul _
    have hHdiff : ∀ i, Differentiable ℂ (fun z => H z i) := by
      intro i
      by_cases hh : h i = 0
      · have e0 : (fun z => H z i) = fun _ => 0 := by
          funext z
          rw [hH]
          change (if h i = 0 then (0 : ℂ) else _) = 0
          rw [ite_eq_left hh]
        rw [e0]
        exact differentiable_const _
      · have e1 : (fun z => H z i) = (fun z =>
          ph h i * Complex.exp (A z * Real.log ‖h i‖)) := by
          funext z
          rw [hH]
          change (if h i = 0 then (0 : ℂ) else _) = _
          rw [ite_eq_right hh]
        rw [e1]
        exact (differentiable_const _).mul
          (Complex.differentiable_exp.comp (hA_diff.mul_const _))
    have hHbdd : ∃ B : α → ℝ, ∀ z ∈
        Complex.HadamardThreeLines.verticalClosedStrip 0 1,
        ∀ i, ‖H z i‖ ≤ B i := by
      refine ⟨fun i => ‖h i‖ ^ (r.toReal * min (r₀⁻¹).toReal (r₁⁻¹).toReal)
        + ‖h i‖ ^ (r.toReal * max (r₀⁻¹).toReal (r₁⁻¹).toReal),
        fun z hz i => ?_⟩
      have hx : z.re ∈ Set.Icc (0 : ℝ) 1 := hz
      obtain ⟨hx0, hx1⟩ := Set.mem_Icc.mp hx
      have hmem0 : (1 - z.re) * (r₀⁻¹).toReal + z.re * (r₁⁻¹).toReal ≤
          max (r₀⁻¹).toReal (r₁⁻¹).toReal := by
        calc (1 - z.re) * (r₀⁻¹).toReal + z.re * (r₁⁻¹).toReal
            ≤ (1 - z.re) * max (r₀⁻¹).toReal (r₁⁻¹).toReal +
              z.re * max (r₀⁻¹).toReal (r₁⁻¹).toReal := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left (le_max_left _ _)
                  (sub_nonneg.mpr hx1)
              · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hx0
          _ = _ := by rw [← add_mul, sub_add_cancel, one_mul]
      have hmem1 : min (r₀⁻¹).toReal (r₁⁻¹).toReal ≤
          (1 - z.re) * (r₀⁻¹).toReal + z.re * (r₁⁻¹).toReal := by
        calc min (r₀⁻¹).toReal (r₁⁻¹).toReal
            = (1 - z.re) * min (r₀⁻¹).toReal (r₁⁻¹).toReal +
              z.re * min (r₀⁻¹).toReal (r₁⁻¹).toReal := by
                rw [← add_mul, sub_add_cancel, one_mul]
          _ ≤ _ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left (min_le_left _ _)
                  (sub_nonneg.mpr hx1)
              · exact mul_le_mul_of_nonneg_left (min_le_right _ _) hx0
      have hlo : r.toReal * min (r₀⁻¹).toReal (r₁⁻¹).toReal ≤ (A z).re := by
        rw [hAre z]
        exact mul_le_mul_of_nonneg_left hmem1 hP.le
      have hhi : (A z).re ≤ r.toReal *
          max (r₀⁻¹).toReal (r₁⁻¹).toReal := by
        rw [hAre z]
        exact mul_le_mul_of_nonneg_left hmem0 hP.le
      rw [hHnorm z i]
      by_cases hh : h i = 0
      · rw [ite_eq_left hh]
        exact add_nonneg (Real.rpow_nonneg (Complex.norm_nonneg _) _)
          (Real.rpow_nonneg (Complex.norm_nonneg _) _)
      · rw [ite_eq_right hh]
        have hpos : 0 < ‖h i‖ := norm_pos_iff.mpr hh
        rcases le_total ‖h i‖ 1 with hle | hle
        · calc ‖h i‖ ^ (A z).re
              ≤ ‖h i‖ ^ (r.toReal * min (r₀⁻¹).toReal (r₁⁻¹).toReal) :=
                Real.rpow_le_rpow_of_exponent_ge hpos hle hlo
            _ ≤ _ + _ := le_add_of_nonneg_right
                (Real.rpow_nonneg (Complex.norm_nonneg _) _)
        · calc ‖h i‖ ^ (A z).re
              ≤ ‖h i‖ ^ (r.toReal * max (r₀⁻¹).toReal (r₁⁻¹).toReal) :=
                Real.rpow_le_rpow_of_exponent_le hle hhi
            _ ≤ _ + _ := le_add_of_nonneg_left
                (Real.rpow_nonneg (Complex.norm_nonneg _) _)
    exact ⟨H, hHθ, bnd0, bnd1, hHdiff, hHbdd⟩

lemma unit_bound {ι κ : Type*} [Finite ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    {p₀ p₁ q₀ q₁ p q : ENNReal} {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hp_eq : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq_eq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    {M₀ M₁ : ENNReal} (hM₀ : M₀ ≠ ⊤) (hM₁ : M₁ ≠ ⊤)
    (T : (ι → Complex) →ₗ[Complex] (κ → Complex))
    (h₀ : ∀ f : ι → Complex,
      eLpNorm (T f) q₀ (Measure.count : Measure κ) ≤
        M₀ * eLpNorm f p₀ (Measure.count : Measure ι))
    (h₁ : ∀ f : ι → Complex,
      eLpNorm (T f) q₁ (Measure.count : Measure κ) ≤
        M₁ * eLpNorm f p₁ (Measure.count : Measure ι))
    {q₀' q₁' q' : ENNReal}
    (hq₀c : q₀⁻¹ + q₀'⁻¹ = 1) (hq₁c : q₁⁻¹ + q₁'⁻¹ = 1)
    (hqc : q⁻¹ + q'⁻¹ = 1)
    {f : ι → Complex}
    (hf : eLpNorm f p (Measure.count : Measure ι) = 1)
    {g : κ → Complex}
    (hg : eLpNorm g q' (Measure.count : Measure κ) = 1) :
    ‖∑ k, (T f) k * g k‖ ≤ M₀.toReal ^ (1 - θ) * M₁.toReal ^ θ := by
  have := Fintype.ofFinite ι
  classical
  have hq1 : 1 ≤ q := q_ge_one_of_conj hqc
  have hq0n : q₀ ≠ 0 := ne_of_gt (one_pos.trans_le hq₀)
  have hq1n : q₁ ≠ 0 := ne_of_gt (one_pos.trans_le hq₁)
  have hqn : q ≠ 0 := ne_of_gt (one_pos.trans_le hq1)
  have f0 : q₀⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hq0n
  have f1 : q₁⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hq1n
  have f0' : q₀'⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (q'_ne_zero_of_conj hq₀c)
  have f1' : q₁'⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (q'_ne_zero_of_conj hq₁c)
  have f'' : q'⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (q'_ne_zero_of_conj hqc)
  have e0 : (q₀⁻¹).toReal + (q₀'⁻¹).toReal = 1 := by
    have h := congrArg ENNReal.toReal hq₀c
    rwa [ENNReal.toReal_add f0 f0', ENNReal.toReal_one] at h
  have e1 : (q₁⁻¹).toReal + (q₁'⁻¹).toReal = 1 := by
    have h := congrArg ENNReal.toReal hq₁c
    rwa [ENNReal.toReal_add f1 f1', ENNReal.toReal_one] at h
  have eq' : (q⁻¹).toReal =
      (1 - θ) * (q₀⁻¹).toReal + θ * (q₁⁻¹).toReal := by
    have h := congrArg ENNReal.toReal hq_eq
    rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top f0)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top f1),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hθ₁.le),
      ENNReal.toReal_ofReal hθ₀.le] at h
    exact h
  have ereal : (q'⁻¹).toReal =
      (1 - θ) * (q₀'⁻¹).toReal + θ * (q₁'⁻¹).toReal := by
    have e0' : (q₀'⁻¹).toReal = 1 - (q₀⁻¹).toReal := by linarith [e0]
    have e1' : (q₁'⁻¹).toReal = 1 - (q₁⁻¹).toReal := by linarith [e1]
    have h := congrArg ENNReal.toReal hqc
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hqn) f'',
      ENNReal.toReal_one] at h
    have ee' : (q'⁻¹).toReal = 1 - (q⁻¹).toReal := by linarith [h]
    rw [e0', e1', ee', eq']
    ring
  have hq'_eq : q'⁻¹ = ENNReal.ofReal (1 - θ) * q₀'⁻¹ +
      ENNReal.ofReal θ * q₁'⁻¹ := by
    have h1 : q'⁻¹ = ENNReal.ofReal (q'⁻¹).toReal :=
      (ENNReal.ofReal_toReal f'').symm
    rw [h1, ereal, ENNReal.ofReal_add
      (mul_nonneg (sub_nonneg.mpr hθ₁.le) ENNReal.toReal_nonneg)
      (mul_nonneg hθ₀.le ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul (sub_nonneg.mpr hθ₁.le),
      ENNReal.ofReal_mul hθ₀.le,
      ENNReal.ofReal_toReal f0', ENNReal.ofReal_toReal f1']
  have hq₀'1 : 1 ≤ q₀' := q_ge_one_of_conj (by rw [add_comm]; exact hq₀c)
  have hq₁'1 : 1 ≤ q₁' := q_ge_one_of_conj (by rw [add_comm]; exact hq₁c)
  obtain ⟨F, hFθ, hF0, hF1, hFdiff, hFbdd⟩ :=
    fam_bound f hp₀ hp₁ hp_eq hθ₀ hθ₁ hf
  obtain ⟨G, hGθ, hG0, hG1, hGdiff, hGbdd⟩ :=
    fam_bound g hq₀'1 hq₁'1 hq'_eq hθ₀ hθ₁ hg
  have hTv : ∀ v : ι → Complex,
      T v = ∑ i, v i • T (Pi.single i 1) := by
    intro v
    have hvv : v = ∑ i, v i • Pi.single i 1 := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
    conv_lhs => rw [hvv]
    rw [map_sum]
    apply Finset.sum_congr rfl; intro i _
    exact map_smul T _ _
  have hTk : ∀ z k, (T (F z)) k =
      ∑ i, F z i * (T (Pi.single i 1)) k := by
    intro z k
    rw [hTv (F z), Finset.sum_apply]
    apply Finset.sum_congr rfl; intro i _
    rw [Pi.smul_apply, smul_eq_mul]
  have hTdiff : ∀ k, Differentiable ℂ (fun z => (T (F z)) k) := by
    intro k
    have e1 : (fun z => (T (F z)) k) =
        (fun z => ∑ i, F z i * (T (Pi.single i 1)) k) :=
      funext fun z => hTk z k
    have e2 : (fun z => ∑ i, F z i * (T (Pi.single i 1)) k) =
        ∑ i, (fun z => F z i * (T (Pi.single i 1)) k) := by
      funext z
      exact (Finset.sum_apply z Finset.univ (fun i z => F z i * (T (Pi.single i 1)) k)).symm
    rw [e1, e2]
    exact Differentiable.sum (fun i _ => (hFdiff i).mul_const _)
  have hΦdiff : Differentiable ℂ
      (fun z => ∑ k, (T (F z)) k * G z k) := by
    have e3 : (fun z => ∑ k, (T (F z)) k * G z k) =
        ∑ k, (fun z => (T (F z)) k * G z k) := by
      funext z
      exact (Finset.sum_apply z Finset.univ
        (fun k z => (T (F z)) k * G z k)).symm
    rw [e3]
    exact Differentiable.sum (fun k _ => (hTdiff k).mul (hGdiff k))
  have hDCC : DiffContOnCl ℂ (fun z => ∑ k, (T (F z)) k * G z k)
      (Complex.HadamardThreeLines.verticalStrip 0 1) :=
    hΦdiff.diffContOnCl
  have hBdd : BddAbove (norm ∘ (fun z => ∑ k, (T (F z)) k * G z k) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    obtain ⟨BF, hBF⟩ := hFbdd
    obtain ⟨BG, hBG⟩ := hGbdd
    refine ⟨∑ k, (∑ i, BF i * ‖(T (Pi.single i 1)) k‖) * BG k, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖∑ k, (T (F z)) k * G z k‖ ≤ _
    have hTkB : ∀ k, ‖(T (F z)) k‖ ≤
        ∑ i, BF i * ‖(T (Pi.single i 1)) k‖ := by
      intro k
      calc ‖(T (F z)) k‖ = ‖∑ i, F z i * (T (Pi.single i 1)) k‖ := by
              rw [hTk z k]
        _ ≤ ∑ i, ‖F z i * (T (Pi.single i 1)) k‖ := norm_sum_le _ _
        _ = ∑ i, ‖F z i‖ * ‖(T (Pi.single i 1)) k‖ := by
              apply Finset.sum_congr rfl; intro i _
              exact norm_mul _ _
        _ ≤ _ := by
              apply Finset.sum_le_sum; intro i _
              exact mul_le_mul_of_nonneg_right (hBF z hz i) (norm_nonneg _)
    calc ‖∑ k, (T (F z)) k * G z k‖
        ≤ ∑ k, ‖(T (F z)) k * G z k‖ := norm_sum_le _ _
      _ = ∑ k, ‖(T (F z)) k‖ * ‖G z k‖ := by
            apply Finset.sum_congr rfl; intro k _
            exact norm_mul _ _
      _ ≤ _ := by
            apply Finset.sum_le_sum; intro k _
            exact mul_le_mul (hTkB k) (hBG z hz k) (norm_nonneg _)
              (Finset.sum_nonneg fun i _ =>
                mul_nonneg (le_trans (norm_nonneg _) (hBF z hz i))
                  (norm_nonneg _))
  have bndry0 : ∀ z : ℂ, z.re = 0 →
      ‖∑ k, (T (F z)) k * G z k‖ ≤ M₀.toReal := by
    intro z hz
    have hle : ‖∑ k, (T (F z)) k * G z k‖ₑ ≤ M₀ := by
      calc ‖∑ k, (T (F z)) k * G z k‖ₑ
          ≤ eLpNorm (T (F z)) q₀ _ * eLpNorm (G z) q₀' _ :=
            pairing_le _ _ hq₀c
        _ = eLpNorm (T (F z)) q₀ _ * 1 := by rw [hG0 z hz]
        _ = eLpNorm (T (F z)) q₀ _ := mul_one _
        _ ≤ M₀ * eLpNorm (F z) p₀ _ := h₀ _
        _ = M₀ * 1 := by rw [hF0 z hz]
        _ = M₀ := mul_one _
    calc ‖∑ k, (T (F z)) k * G z k‖
        = (‖∑ k, (T (F z)) k * G z k‖ₑ).toReal := by
          rw [enorm_complex_eq_ofReal,
            ENNReal.toReal_ofReal (norm_nonneg _)]
      _ ≤ M₀.toReal := ENNReal.toReal_mono hM₀ hle
  have bndry1 : ∀ z : ℂ, z.re = 1 →
      ‖∑ k, (T (F z)) k * G z k‖ ≤ M₁.toReal := by
    intro z hz
    have hle : ‖∑ k, (T (F z)) k * G z k‖ₑ ≤ M₁ := by
      calc ‖∑ k, (T (F z)) k * G z k‖ₑ
          ≤ eLpNorm (T (F z)) q₁ _ * eLpNorm (G z) q₁' _ :=
            pairing_le _ _ hq₁c
        _ = eLpNorm (T (F z)) q₁ _ * 1 := by rw [hG1 z hz]
        _ = eLpNorm (T (F z)) q₁ _ := mul_one _
        _ ≤ M₁ * eLpNorm (F z) p₁ _ := h₁ _
        _ = M₁ * 1 := by rw [hF1 z hz]
        _ = M₁ := mul_one _
    calc ‖∑ k, (T (F z)) k * G z k‖
        = (‖∑ k, (T (F z)) k * G z k‖ₑ).toReal := by
          rw [enorm_complex_eq_ofReal,
            ENNReal.toReal_ofReal (norm_nonneg _)]
      _ ≤ M₁.toReal := ENNReal.toReal_mono hM₁ hle
  have hmem : ((θ : ℝ) : ℂ) ∈
      Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip
    simp only [Set.mem_preimage, Set.mem_Icc, Complex.ofReal_re]
    exact ⟨hθ₀.le, hθ₁.le⟩
  have hmain :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
      (fun z => ∑ k, (T (F z)) k * G z k) hmem hDCC hBdd
      (fun z hz => bndry0 z (by simpa using hz))
      (fun z hz => bndry1 z (by simpa using hz))
  simpa only [hFθ, hGθ, Complex.ofReal_re] using hmain

lemma riesz_thorin_unit {ι κ : Type*} [Finite ι] [Finite κ]
    [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    {p₀ p₁ q₀ q₁ p q : ENNReal} {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    (hp_eq : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq_eq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    {M₀ M₁ : ENNReal} (hM₀ : M₀ ≠ ⊤) (hM₁ : M₁ ≠ ⊤)
    (T : (ι → Complex) →ₗ[Complex] (κ → Complex))
    (h₀ : ∀ f : ι → Complex,
      eLpNorm (T f) q₀ (Measure.count : Measure κ) ≤
        M₀ * eLpNorm f p₀ (Measure.count : Measure ι))
    (h₁ : ∀ f : ι → Complex,
      eLpNorm (T f) q₁ (Measure.count : Measure κ) ≤
        M₁ * eLpNorm f p₁ (Measure.count : Measure ι))
    {q₀' q₁' q' : ENNReal}
    (hq₀c : q₀⁻¹ + q₀'⁻¹ = 1) (hq₁c : q₁⁻¹ + q₁'⁻¹ = 1)
    (hqc : q⁻¹ + q'⁻¹ = 1)
    {f : ι → Complex}
    (hf : eLpNorm f p (Measure.count : Measure ι) = 1) :
    eLpNorm (T f) q (Measure.count : Measure κ) ≤
      ENNReal.ofReal (M₀.toReal ^ (1 - θ) * M₁.toReal ^ θ) := by
  have := Fintype.ofFinite κ
  have := Fintype.ofFinite ι
  classical
  have hq0 : q ≠ 0 := ne_of_gt (one_pos.trans_le hq)
  rcases eq_or_ne (T f) 0 with hTf0 | hTf
  · rw [hTf0, eLpNorm_zero]
    exact zero_le
  · obtain ⟨g, hg1, hgp⟩ := dual_attain (T f) hTf hq hqc
    have hb := unit_bound hθ₀ hθ₁ hp₀ hp₁ hq₀ hq₁ hp_eq hq_eq hM₀ hM₁ T h₀ h₁
      hq₀c hq₁c hqc hf hg1
    have hA : (eLpNorm (T f) q (Measure.count : Measure κ)).toReal =
        ‖∑ k, (T f) k * g k‖ := by
      rw [hgp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ENNReal.toReal_nonneg]
    have hle : (eLpNorm (T f) q (Measure.count : Measure κ)).toReal ≤
        M₀.toReal ^ (1 - θ) * M₁.toReal ^ θ := by
      rw [hA]; exact hb
    have hfin : eLpNorm (T f) q (Measure.count : Measure κ) ≠ ⊤ :=
      eLpNorm_count_ne_top _ hq0
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal hle

lemma riesz_thorin_top {ι κ : Type*} [Finite ι] [Finite κ]
    [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    {p q : ENNReal} {θ : ℝ} {M₀ M₁ : ENNReal}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hp : 1 ≤ p)
    (hM₀ : M₀ ≠ 0) (hM₁ : M₁ ≠ 0) (hT : M₀ = ⊤ ∨ M₁ = ⊤)
    (T : (ι → Complex) →ₗ[Complex] (κ → Complex)) :
    ∀ f : ι → Complex,
      eLpNorm (T f) q (Measure.count : Measure κ) ≤
        (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p (Measure.count : Measure ι) := by
  have := Fintype.ofFinite κ
  have := Fintype.ofFinite ι
  have hp0 : p ≠ 0 := ne_of_gt (one_pos.trans_le hp)
  have h1θ : (0 : ℝ) < 1 - θ := sub_pos.mpr hθ₁
  intro f
  rcases eq_or_ne (eLpNorm f p _) 0 with hf0 | hfn0
  · have hf : f = 0 := (eLpNorm_count_eq_zero_iff hp0 f).mp hf0
    rw [hf]
    simp
  · have hC : M₀ ^ (1 - θ) * M₁ ^ θ = ⊤ := by
      rcases hT with rfl | rfl
      · rw [ENNReal.top_rpow_of_pos h1θ]
        have hne : M₁ ^ θ ≠ 0 := by
          intro hcon
          rw [ENNReal.rpow_eq_zero_iff] at hcon
          rcases hcon with ⟨h0, _⟩ | ⟨hT, hneg⟩
          · exact hM₁ h0
          · exact absurd hneg (not_lt.mpr hθ₀.le)
        exact ENNReal.top_mul hne
      · rw [ENNReal.top_rpow_of_pos hθ₀]
        have hne : M₀ ^ (1 - θ) ≠ 0 := by
          intro hcon
          rw [ENNReal.rpow_eq_zero_iff] at hcon
          rcases hcon with ⟨h0, _⟩ | ⟨hT, hneg⟩
          · exact hM₀ h0
          · exact absurd hneg (not_lt.mpr h1θ.le)
        exact ENNReal.mul_top hne
    rw [hC, ENNReal.top_mul hfn0]
    exact le_top

lemma riesz_thorin_scale {ι κ : Type*} [Finite ι] [Finite κ]
    [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    {p₀ p₁ q₀ q₁ p q : ENNReal} {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hp : 1 ≤ p)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    (hp_eq : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq_eq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    {M₀ M₁ : ENNReal} (hM₀ : M₀ ≠ ⊤) (hM₁ : M₁ ≠ ⊤)
    (T : (ι → Complex) →ₗ[Complex] (κ → Complex))
    (h₀ : ∀ f : ι → Complex,
      eLpNorm (T f) q₀ (Measure.count : Measure κ) ≤
        M₀ * eLpNorm f p₀ (Measure.count : Measure ι))
    (h₁ : ∀ f : ι → Complex,
      eLpNorm (T f) q₁ (Measure.count : Measure κ) ≤
        M₁ * eLpNorm f p₁ (Measure.count : Measure ι)) :
    ∀ f : ι → Complex,
      eLpNorm (T f) q (Measure.count : Measure κ) ≤
        (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p (Measure.count : Measure ι) := by
  have := Fintype.ofFinite κ
  have := Fintype.ofFinite ι
  classical
  have hp0 : p ≠ 0 := ne_of_gt (one_pos.trans_le hp)
  obtain ⟨q₀', hq₀c⟩ := holder_conj hq₀
  obtain ⟨q₁', hq₁c⟩ := holder_conj hq₁
  obtain ⟨q', hqc⟩ := holder_conj hq
  intro f
  rcases eq_or_ne (eLpNorm f p (Measure.count : Measure ι)) 0 with hf0 | hfn0
  · have hf : f = 0 := (eLpNorm_count_eq_zero_iff hp0 f).mp hf0
    rw [hf0, hf, map_zero T, eLpNorm_zero, mul_zero]
  · have hafin : eLpNorm f p (Measure.count : Measure ι) ≠ ⊤ :=
      eLpNorm_count_ne_top _ hp0
    have ha0 : 0 < (eLpNorm f p (Measure.count : Measure ι)).toReal :=
      ENNReal.toReal_pos hfn0 hafin
    have haC : ENNReal.ofReal
        (eLpNorm f p (Measure.count : Measure ι)).toReal =
        eLpNorm f p (Measure.count : Measure ι) :=
      ENNReal.ofReal_toReal hafin
    set f₁ : ι → Complex :=
      (((eLpNorm f p (Measure.count : Measure ι)).toReal⁻¹ : ℝ) : ℂ) • f
      with hf₁
    have hf₁1 : eLpNorm f₁ p (Measure.count : Measure ι) = 1 := by
      rw [hf₁, eLpNorm_const_smul, enorm_complex_eq_ofReal,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (inv_pos.mpr ha0)),
        ENNReal.ofReal_inv_of_pos ha0, haC,
        ENNReal.inv_mul_cancel hfn0 hafin]
    have h1 : (((eLpNorm f p (Measure.count : Measure ι)).toReal : ℝ) : ℂ) *
        ((((eLpNorm f p (Measure.count : Measure ι)).toReal⁻¹ : ℝ)) : ℂ) =
        1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ ha0.ne', Complex.ofReal_one]
    have hff : f =
        (((eLpNorm f p (Measure.count : Measure ι)).toReal : ℝ) : ℂ) • f₁ := by
      funext i
      rw [Pi.smul_apply, hf₁, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        ← mul_assoc, h1, one_mul]
    have hTf : T f =
        (((eLpNorm f p (Measure.count : Measure ι)).toReal : ℝ) : ℂ) •
          T f₁ := by
      conv_lhs => rw [hff]
      exact map_smul T _ _
    have hunit := riesz_thorin_unit hθ₀ hθ₁ hp₀ hp₁ hq₀ hq₁ hq hp_eq hq_eq
      hM₀ hM₁ T h₀ h₁ hq₀c hq₁c hqc hf₁1
    have hCval : ENNReal.ofReal (M₀.toReal ^ (1 - θ) * M₁.toReal ^ θ) =
        M₀ ^ (1 - θ) * M₁ ^ θ := by
      have e1 : M₀ ^ (1 - θ) = ENNReal.ofReal (M₀.toReal ^ (1 - θ)) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
          (sub_nonneg.mpr hθ₁.le),
          ENNReal.ofReal_toReal hM₀]
      have e2 : M₁ ^ θ = ENNReal.ofReal (M₁.toReal ^ θ) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hθ₀.le,
          ENNReal.ofReal_toReal hM₁]
      rw [e1, e2,
        ← ENNReal.ofReal_mul
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
    calc eLpNorm (T f) q (Measure.count : Measure κ)
        = ENNReal.ofReal
            (eLpNorm f p (Measure.count : Measure ι)).toReal *
          eLpNorm (T f₁) q (Measure.count : Measure κ) := by
          rw [hTf, eLpNorm_const_smul, enorm_complex_eq_ofReal,
            Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ENNReal.toReal_nonneg]
      _ ≤ ENNReal.ofReal
            (eLpNorm f p (Measure.count : Measure ι)).toReal *
          ENNReal.ofReal (M₀.toReal ^ (1 - θ) * M₁.toReal ^ θ) :=
          mul_le_mul_right hunit _
      _ = (M₀ ^ (1 - θ) * M₁ ^ θ) *
          eLpNorm f p (Measure.count : Measure ι) := by
          rw [hCval, haC]
          exact mul_comm _ _

/-- Finite-hypothesis form of `riesz_thorin` below: the same interpolation bound
under `[Finite ι] [Finite κ]`, installing `Fintype.ofFinite` locally where finite
sums require it. `riesz_thorin` is the `Fintype` specialization, proved from this. -/
theorem riesz_thorin_finite
    {ι κ : Type*} [Finite ι] [Finite κ]
    [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    {p₀ p₁ q₀ q₁ p q : ENNReal}
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hp : 1 ≤ p)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    (hp_eq : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq_eq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    {M₀ M₁ : ENNReal}
    (T : (ι → Complex) →ₗ[Complex] (κ → Complex))
    (h₀ : ∀ f : ι → Complex,
      eLpNorm (T f) q₀ (Measure.count : Measure κ) ≤
        M₀ * eLpNorm f p₀ (Measure.count : Measure ι))
    (h₁ : ∀ f : ι → Complex,
      eLpNorm (T f) q₁ (Measure.count : Measure κ) ≤
        M₁ * eLpNorm f p₁ (Measure.count : Measure ι)) :
    ∀ f : ι → Complex,
      eLpNorm (T f) q (Measure.count : Measure κ) ≤
        (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p (Measure.count : Measure ι) := by
  classical
  rcases eq_or_ne θ 0 with rfl | hθne0
  · have hp0e : p⁻¹ = p₀⁻¹ := by simpa using hp_eq
    have hq0e : q⁻¹ = q₀⁻¹ := by simpa using hq_eq
    have hpp : p = p₀ := by
      have h := congrArg Inv.inv hp0e
      rwa [inv_inv, inv_inv] at h
    have hqq : q = q₀ := by
      have h := congrArg Inv.inv hq0e
      rwa [inv_inv, inv_inv] at h
    intro f
    rw [hpp, hqq]
    simp only [sub_zero, ENNReal.rpow_one, ENNReal.rpow_zero, mul_one]
    exact h₀ f
  rcases eq_or_ne θ 1 with rfl | hθne1
  · have hp1e : p⁻¹ = p₁⁻¹ := by simpa using hp_eq
    have hq1e : q⁻¹ = q₁⁻¹ := by simpa using hq_eq
    have hpp : p = p₁ := by
      have h := congrArg Inv.inv hp1e
      rwa [inv_inv, inv_inv] at h
    have hqq : q = q₁ := by
      have h := congrArg Inv.inv hq1e
      rwa [inv_inv, inv_inv] at h
    intro f
    rw [hpp, hqq]
    simp only [sub_self, ENNReal.rpow_zero, ENNReal.rpow_one, one_mul]
    exact h₁ f
  have hθpos : 0 < θ := lt_of_le_of_ne hθ₀ (Ne.symm hθne0)
  have hθlt1 : θ < 1 := lt_of_le_of_ne hθ₁ hθne1
  have h1θ : (0 : ℝ) < 1 - θ := sub_pos.mpr hθlt1
  rcases eq_or_ne M₀ 0 with rfl | hM₀0
  · intro f
    have hq00 : q₀ ≠ 0 := ne_of_gt (one_pos.trans_le hq₀)
    have hTf : T f = 0 := by
      have h0f := h₀ f
      rw [zero_mul] at h0f
      have hz : eLpNorm (T f) q₀ (Measure.count : Measure κ) = 0 :=
        le_antisymm h0f zero_le
      exact (eLpNorm_count_eq_zero_iff hq00 (T f)).mp hz
    have hRHS : ((0 : ENNReal) ^ (1 - θ) * M₁ ^ θ) *
        eLpNorm f p (Measure.count : Measure ι) = 0 := by
      rw [ENNReal.zero_rpow_of_pos h1θ, zero_mul, zero_mul]
    rw [hTf, eLpNorm_zero, hRHS]
  rcases eq_or_ne M₁ 0 with rfl | hM₁0
  · intro f
    have hq10 : q₁ ≠ 0 := ne_of_gt (one_pos.trans_le hq₁)
    have hTf : T f = 0 := by
      have h1f := h₁ f
      rw [zero_mul] at h1f
      have hz : eLpNorm (T f) q₁ (Measure.count : Measure κ) = 0 :=
        le_antisymm h1f zero_le
      exact (eLpNorm_count_eq_zero_iff hq10 (T f)).mp hz
    have hRHS : (M₀ ^ (1 - θ) * (0 : ENNReal) ^ θ) *
        eLpNorm f p (Measure.count : Measure ι) = 0 := by
      rw [ENNReal.zero_rpow_of_pos hθpos, mul_zero, zero_mul]
    rw [hTf, eLpNorm_zero, hRHS]
  rcases eq_or_ne M₀ ⊤ with rfl | hM₀T
  · exact riesz_thorin_top hθpos hθlt1 hp (by simp) hM₁0 (Or.inl rfl) T
  · rcases eq_or_ne M₁ ⊤ with rfl | hM₁T
    · exact riesz_thorin_top hθpos hθlt1 hp hM₀0 (by simp) (Or.inr rfl) T
    · exact riesz_thorin_scale hθpos hθlt1 hp₀ hp₁ hp hq₀ hq₁ hq hp_eq hq_eq
        hM₀T hM₁T T h₀ h₁

/--
For finite `ι, κ` with counting measure, if `T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)` has `ℓ^{p₀} → ℓ^{q₀}`
bound `M₀` and `ℓ^{p₁} → ℓ^{q₁}` bound `M₁` and `1/p = (1-θ)/p₀ + θ/p₁`, `1/q = (1-θ)/q₀ + θ/q₁`
with `θ ∈ [0, 1]`, then `eLpNorm (T f) q ≤ (M₀^(1-θ) * M₁^θ) * eLpNorm f p` for all `f`. Source:
M. Riesz, Sur les maxima des formes bilinéaires et sur les fonctionnelles linéaires,
Acta Math. 49 (1927), 465–497, DOI 10.1007/BF02564121; and G. O. Thorin, Convexity theorems
generalizing those of M. Riesz and Hadamard with some applications,
Comm. Sem. Math. Univ. Lund 9 (1948), 1–58, Riesz-Thorin interpolation theorem; Stein-Shakarchi
Complex interpolation; Lean states finite counting-measure complex `→ₗ[ℂ]` form with explicit
interpolation identities `p⁻¹=(1-θ)p₀⁻¹+θp₁⁻¹` and bound `M₀^(1-θ)M₁^θ`.

Proves `Wanted` entry `riesz_thorin`.
-/
theorem riesz_thorin
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    {p₀ p₁ q₀ q₁ p q : ENNReal}
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hp : 1 ≤ p)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    (hp_eq : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq_eq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    {M₀ M₁ : ENNReal}
    (T : (ι → Complex) →ₗ[Complex] (κ → Complex))
    (h₀ : ∀ f : ι → Complex,
      eLpNorm (T f) q₀ (Measure.count : Measure κ) ≤
        M₀ * eLpNorm f p₀ (Measure.count : Measure ι))
    (h₁ : ∀ f : ι → Complex,
      eLpNorm (T f) q₁ (Measure.count : Measure κ) ≤
        M₁ * eLpNorm f p₁ (Measure.count : Measure ι)) :
    ∀ f : ι → Complex,
      eLpNorm (T f) q (Measure.count : Measure κ) ≤
        (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p (Measure.count : Measure ι) := by
  exact riesz_thorin_finite hθ₀ hθ₁ hp₀ hp₁ hp hq₀ hq₁ hq hp_eq hq_eq T h₀ h₁

end FunctionalAnalysis.RieszThorinWanted
end
