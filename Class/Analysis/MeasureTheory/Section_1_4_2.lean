import Mathlib.SetTheory.Cardinal.Aleph
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4


/-!
# Introduction to Measure Theory, Section 1.4.2: $\sigma$-algebras and measurable spaces

A companion to (the introduction to) Section 1.4.2 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.4.12 (Sigma algebra) -/
class ConcreteSigmaAlgebra (X:Type*) extends ConcreteBooleanAlgebra X where
  countable_union_mem : ∀ E : ℕ → Set X,
    (∀ n, toConcreteBooleanAlgebra.measurable (E n)) → toConcreteBooleanAlgebra.measurable (⋃ n, E n)

