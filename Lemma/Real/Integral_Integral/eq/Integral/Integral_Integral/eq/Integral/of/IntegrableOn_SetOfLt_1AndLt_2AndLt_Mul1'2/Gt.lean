import Mathlib
import sympy.Basic
open MeasureTheory Set


private lemma section_fst (v : ℝ) (hv : 0 < v) (f : ℝ × ℝ → ℂ) (σ : ℝ) :
  (∫ w : ℝ, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f (σ, w))
    = (Ioi (0 : ℝ)).indicator (fun σ : ℝ => ∫ w in Ioi (v / σ), f (σ, w)) σ := by
  if hσ : 0 < σ then
    rw [indicator_of_mem (mem_Ioi.mpr hσ), ← integral_indicator measurableSet_Ioi]
    congr 1
    funext w
    have hiff : (σ, w) ∈ {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} ↔ w ∈ Ioi (v / σ) := by
      simp only [mem_ofPred_eq, mem_Ioi]
      constructor
      ·
        rintro ⟨-, -, h⟩
        rw [div_lt_iff₀ hσ]
        linarith [mul_comm σ w]
      ·
        intro h
        have h' := (div_lt_iff₀ hσ).mp h
        refine ⟨hσ, ?_, by linarith [mul_comm σ w]⟩
        by_contra hw'
        have hw'' := not_lt.mp hw'
        nlinarith
    if hmem : w ∈ Ioi (v / σ) then
      rw [indicator_of_mem hmem, indicator_of_mem (hiff.mpr hmem)]
    else
      rw [indicator_of_notMem hmem, indicator_of_notMem (fun h => hmem (hiff.mp h))]
  else
    rw [indicator_of_notMem (fun h : σ ∈ Ioi (0:ℝ) => hσ (mem_Ioi.mp h))]
    have hzero : ∀ w : ℝ, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f (σ, w) = 0 := by
      intro w
      apply indicator_of_notMem
      intro h
      exact hσ h.1
    simp [hzero]
private lemma section_snd (v : ℝ) (hv : 0 < v) (f : ℝ × ℝ → ℂ) (w : ℝ) :
  (∫ σ : ℝ, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f (σ, w))
    = (Ioi (0 : ℝ)).indicator (fun w : ℝ => ∫ σ in Ioi (v / w), f (σ, w)) w := by
  if hw : 0 < w then
    rw [indicator_of_mem (mem_Ioi.mpr hw), ← integral_indicator measurableSet_Ioi]
    congr 1
    funext σ
    have hiff : (σ, w) ∈ {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} ↔ σ ∈ Ioi (v / w) := by
      simp only [mem_ofPred_eq, mem_Ioi]
      constructor
      ·
        rintro ⟨-, -, h⟩
        rw [div_lt_iff₀ hw]
        linarith
      ·
        intro h
        have h' := (div_lt_iff₀ hw).mp h
        refine ⟨?_, hw, by linarith⟩
        by_contra hs
        have hs' := not_lt.mp hs
        nlinarith
    if hmem : σ ∈ Ioi (v / w) then
      rw [indicator_of_mem hmem, indicator_of_mem (hiff.mpr hmem)]
    else
      rw [indicator_of_notMem hmem, indicator_of_notMem (fun h => hmem (hiff.mp h))]
  else
    rw [indicator_of_notMem (fun h : w ∈ Ioi (0:ℝ) => hw (mem_Ioi.mp h))]
    have hzero : ∀ σ : ℝ, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f (σ, w) = 0 := by
      intro σ
      apply indicator_of_notMem
      intro h
      exact hw h.2.1
    simp [hzero]
private lemma measurableSet_region (v : ℝ) :
  MeasurableSet {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} :=
  (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_const (measurable_fst.mul measurable_snd)))

private lemma helper_main (v : ℝ) (hv : 0 < v) (f : ℝ × ℝ → ℂ)
  (hf : IntegrableOn f {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}) :
  (∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q ∧
    (∫ w in Ioi (0 : ℝ), ∫ σ in Ioi (v / w), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q := by
  have hR := measurableSet_region v
  have hint : Integrable ({q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f)
    ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have := hf.integrable_indicator hR
    rwa [Measure.volume_eq_prod] at this
  have key : ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q =
    ∫ q, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f q
      ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [integral_indicator hR, Measure.volume_eq_prod]
  constructor
  ·
    rw [key, integral_prod _ hint, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext σ
    exact (section_fst v hv f σ).symm
  ·
    rw [key, integral_prod_symm _ hint, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext w
    exact (section_snd v hv f w).symm
/--
[LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion.lean)
-/
@[path]
private lemma main
  {v : ℝ}
  {f : ℝ × ℝ → ℂ}
-- given
  (hv : 0 < v)
  (hf : IntegrableOn f {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}) :
-- imply
  (∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q ∧
      (∫ w in Ioi (0 : ℝ), ∫ σ in Ioi (v / w), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q :=
-- proof
  helper_main v hv f hf


-- created on 2026-10-23
