module
public import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Topology.Instances.Irrational
public import Theorem.Analysis.MeasureTheory.Section_1_2_0
open BoundedInterval


public section

/-!
# Introduction to Measure Theory, Section 1.2: Lebesgue measure

A companion to (the introduction to) Section 1.2 of the book "An introduction to Measure Theory".

-/
/-- This definition deviates from the text by working with countable families of boxes rather than boxes indexed by the natural numbers.  This becomes important in dimension zero, when all boxes are non-empty. -/
noncomputable def Lebesgue_outer_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : EReal :=
  sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }

