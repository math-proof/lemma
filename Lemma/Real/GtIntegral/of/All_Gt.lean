import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import sympy.Basic


@[main]
private lemma ioo
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hab : a < b)
  (hfi : IntervalIntegrable f MeasureTheory.volume a b)
  (hgi : IntervalIntegrable g MeasureTheory.volume a b)
  (h : ∀ x ∈ Set.Ioo a b, f x > g x) :
-- imply
  (∫ x : ℝ in a..b, f x) > (∫ x : ℝ in a..b, g x) := by
-- proof
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on (hfi.sub hgi)
    (fun x hx ↦ sub_pos.mpr (h x hx)) hab
  rw [intervalIntegral.integral_sub hfi hgi] at hpos
  exact sub_pos.mp hpos


@[main]
private lemma main
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hab : a < b)
  (hfi : IntervalIntegrable f MeasureTheory.volume a b)
  (hgi : IntervalIntegrable g MeasureTheory.volume a b)
  (h : ∀ x ∈ Set.Ioc a b, f x > g x) :
-- imply
  (∫ x : ℝ in a..b, f x) > (∫ x : ℝ in a..b, g x) := by
-- proof
  exact ioo hab hfi hgi
    fun x hx ↦ h x (Set.Ioo_subset_Ioc_self hx)


@[main]
private lemma ico
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hab : a < b)
  (hfi : IntervalIntegrable f MeasureTheory.volume a b)
  (hgi : IntervalIntegrable g MeasureTheory.volume a b)
  (h : ∀ x ∈ Set.Ico a b, f x > g x) :
-- imply
  (∫ x : ℝ in a..b, f x) > (∫ x : ℝ in a..b, g x) := by
-- proof
  exact ioo hab hfi hgi
    fun x hx ↦ h x (Set.Ioo_subset_Ico_self hx)


@[main]
private lemma icc
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hab : a < b)
  (hfi : IntervalIntegrable f MeasureTheory.volume a b)
  (hgi : IntervalIntegrable g MeasureTheory.volume a b)
  (h : ∀ x ∈ Set.Icc a b, f x > g x) :
-- imply
  (∫ x : ℝ in a..b, f x) > (∫ x : ℝ in a..b, g x) := by
-- proof
  exact main hab hfi hgi
    fun x hx ↦ h x (Set.Ioc_subset_Icc_self hx)


-- created on 2026-09-10
