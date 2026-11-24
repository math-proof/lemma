module
public import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Topology.Instances.Irrational
public import Theorem.Analysis.MeasureTheory.Section_1_2_0.Part2
open BoundedInterval


public section

/-!
# Introduction to Measure Theory, Section 1.2: Lebesgue measure

A companion to (the introduction to) Section 1.2 of the book "An introduction to Measure Theory".

-/
def LebesgueMeasurable {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop :=
  ∀ ε > 0, ∃ U: Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure (U \ E) ≤ ε

-- The Lebesgue measure of a set (equals its Lebesgue outer measure).
noncomputable def Lebesgue_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : EReal := Lebesgue_outer_measure E

