module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Module

public section

open Finset MeasureTheory
open scoped ENNReal


/--
The empirical measure of a positive number of sample points is a probability measure: the
normalized sum of Dirac masses at those points has total mass one.
-/
public theorem Random.IsProbabilityMeasure.of.Gt_0
  [MeasurableSpace α]
  {n : ℕ} {ω : Fin n → α}
-- given
  (hn : 0 < n) :
-- imply
  IsProbabilityMeasure ((n : ENNReal)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i)) :=
-- proof
by
  constructor
  simp only [Measure.smul_apply, smul_eq_mul]
  have hsum : (∑ i : Fin n, Measure.dirac (ω i)) Set.univ = n := by
    rw [Measure.coe_finsetSum]
    simp [Finset.sum_const, Finset.card_univ]
  rw [hsum]
  exact ENNReal.inv_mul_cancel (by simpa using hn.ne') (by simp)


-- created on 2026-11-02
