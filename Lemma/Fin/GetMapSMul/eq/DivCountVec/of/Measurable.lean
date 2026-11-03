import Lemma.Fin.Pi_ToMeasure.of.EqSum
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Module
import Initialize.Tactic.Attr.Basic
open Classical Fin Finset MeasureTheory
open scoped ENNReal


/--
The cell masses of the empirical measure of finitely many sample points are the empirical
frequencies. For a measurable observable, the pushed-forward mass of a cell is the number of
samples in that cell divided by the sample size.
-/
@[path]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
  {n : ℕ} {ω : Fin n → α} {φ : α → β} {a : β}
-- given
  (hφ : Measurable φ) :
-- imply
  (((n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i)).map φ) {a} =
    (countVec (fun i => φ (ω i)) a : ℝ≥0∞) / n :=
-- proof
by
  have hsing : MeasurableSet ({a} : Set β) := measurableSet_singleton a
  rw [Measure.map_apply hφ hsing, Measure.smul_apply, smul_eq_mul, Measure.coe_finsetSum]
  have hpre : MeasurableSet (φ ⁻¹' {a}) := hφ hsing
  have hdirac : ∀ i, Measure.dirac (ω i) (φ ⁻¹' {a}) =
      if φ (ω i) = a then 1 else 0 := by
    intro i
    rw [Measure.dirac_apply' (ω i) hpre]
    if h : φ (ω i) = a then
      simp [h]
    else
      simp [h]
  simp only [hdirac, countVec, Finset.sum_apply, ENNReal.div_eq_inv_mul]
  rw [Nat.cast_sum]
  refine congrArg (fun t => (n : ℝ≥0∞)⁻¹ * t) (Finset.sum_congr rfl fun i _ => ?_)
  if h : φ (ω i) = a then
    simp [h]
  else
    simp [h]


-- created on 2026-11-02
