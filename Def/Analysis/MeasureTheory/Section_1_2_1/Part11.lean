module
public import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
public import Theorem.Analysis.Misc.RealERealENNReal
public import Theorem.Analysis.Misc.Combinatorics
public import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part12
open BoundedInterval


public section

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/
def IsCube {d:ℕ} (B: Box d) : Prop := ∃ r, ∀ i, |B.side i|ₗ = r

noncomputable def DyadicCube {d:ℕ} (n:ℤ) (a: Fin d → ℤ) : Box d := { side := fun i ↦ Icc (a i/2^n) ((a i + 1)/2^n) }

