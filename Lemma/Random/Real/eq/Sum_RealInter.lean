import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Fintype.Basic
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ι : Type*} [Fintype ι]
-- given
  (B : Set Ω)
  (L : Ω → ι) :
-- imply
  μ.real B = ∑ i, μ.real (B ∩ {ω | L ω = i}) := by
-- proof
  classical
  rw [← measureReal_biUnion_finset (fun i _ j _ hij => Set.disjoint_left.mpr fun ω h₁ h₂ => hij (h₁.2.symm.trans h₂.2)) fun _ _ => .of_discrete]
  congr 1
  ext
  simp


-- created on 2026-09-26
