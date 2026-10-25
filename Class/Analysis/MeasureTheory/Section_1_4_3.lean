import Def.Analysis.MeasureTheory.Section_1_4_2.Part8


/-!
# Introduction to Measure Theory, Section 1.4.3: Countably additive measures and measure spaces

A companion to (the introduction to) Section 1.4.3 of the book "An introduction to Measure Theory".

Note: initially this section will use custom-notions of concrete sigma algebras and countably additive measures, but will transition to the Mathlib notions of {name}`Measurable` and {name}`MeasureTheory.Measure`, which will be in use going forward. In particular, exercises past this point will be easier
to solve using the Mathlib library for measure theory than the custom results defined here.
-/

/-- Definition 1.4.19 (Finitely additive measure) -/
class FinitelyAdditiveMeasure {X:Type*} (B: ConcreteBooleanAlgebra X) where
  measure : Set X → EReal
  measure_pos : ∀ A : Set X, B.measurable A → 0 ≤ measure A
  measure_empty : measure ∅ = 0
  measure_finite_additive : ∀ E F : Set X, B.measurable E → B.measurable F → Disjoint E F →
    measure (E ∪ F) = measure E + measure F

