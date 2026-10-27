import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory Filter Topology Set


/--
[integrableOn_g_Ioc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem168LowerBound.lean)
-/
@[path]
lemma integrableOn_g_Ioc
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hf_mono : Monotone f)
  (ha : 0 < a)
  (hab : a ≤ b) :
-- imply
  IntegrableOn (fun t => (f t - t) / t ^ 2) (Ioc a b) := by
-- proof
  have hfm : Measurable (fun t : ℝ => (f t - t) / t ^ 2) :=
    (hf_mono.measurable.sub measurable_id).div (measurable_id.pow_const 2)
  refine IntegrableOn.of_bound
    (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
    (hf := hfm.aestronglyMeasurable.restrict)
    (C := (|f a| + |f b| + b) / a ^ 2) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  apply ae_of_all; intro t ht
  have hta : a ≤ t := le_of_lt ht.1
  have htb : t ≤ b := ht.2
  have ht_pos : 0 < t := lt_of_lt_of_le ha hta
  simp only [Real.norm_eq_abs]
  rw [abs_div, abs_pow, abs_of_pos ht_pos]
  have hfa : f a ≤ f t := hf_mono hta
  have hfb : f t ≤ f b := hf_mono htb
  have hnum : |f t - t| ≤ |f a| + |f b| + b := by
    obtain h | h := le_or_gt (f t) t
    · rw [abs_of_nonpos (by linarith)]
      linarith [abs_nonneg (f b), neg_abs_le (f a)]
    · rw [abs_of_pos (by linarith)]
      linarith [abs_nonneg (f a), le_abs_self (f b)]
  have hdenom : a ^ 2 ≤ t ^ 2 := sq_le_sq' (by linarith) hta
  calc |f t - t| / t ^ 2
    ≤ |f t - t| / a ^ 2 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos ha) hdenom
    _ ≤ (|f a| + |f b| + b) / a ^ 2 :=
      div_le_div_of_nonneg_right hnum (le_of_lt (sq_pos_of_pos ha))

/--
[setIntegral_Ioc_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem168LowerBound.lean)
-/
@[path]
lemma setIntegral_Ioc_split
  {g : ℝ → ℝ}
  {a b c : ℝ}
-- given
  (hab : a ≤ b)
  (hbc : b ≤ c)
  (hg1 : IntegrableOn g (Ioc a b))
  (hg2 : IntegrableOn g (Ioc b c)) :
-- imply
  ∫ t in Ioc a c, g t = (∫ t in Ioc a b, g t) + ∫ t in Ioc b c, g t := by
-- proof
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc]
  exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hg1 hg2


-- created on 2026-10-23
