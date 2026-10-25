import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part6
open BoundedInterval

@[ext]
/-!
# Introduction to Measure Theory, Section 1.1.3: Connections with the Riemann integral

A companion to Section 1.1.3 of the book "An introduction to Measure Theory".

-/


/-- Definition 1.1.6 (Darboux integral, integrability) -/
-- A function is Darboux integrable if it is bounded on a nonempty closed interval and its
-- lower and upper Darboux integrals coincide. Nonemptiness matches {name}`RiemannIntegrableOn`.
noncomputable def DarbouxIntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) : Prop :=
  (I = Icc I.a I.b) ∧ I.toSet.Nonempty ∧
    (∃ M, ∀ x ∈ I, |f x| ≤ M) ∧ LowerDarbouxIntegral f I = UpperDarbouxIntegral f I

/-- We give the Darboux integral the "junk" value of the lower Darboux integral when the function is not integrable. -/
-- The Darboux integral: equals the common value if integrable, otherwise the lower Darboux integral.
noncomputable def darbouxIntegral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ := LowerDarbouxIntegral f I

