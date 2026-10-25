import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic


/-!
# Introduction to Measure Theory, Section 1.1.2: Jordan measure

A companion to Section 1.1.2 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.1.4.  We intend these concepts to only be applied for bounded sets {lean}`E`, but
it is convenient to permit {lean}`E` to be unbounded for the purposes of making the definitions.
-/
noncomputable abbrev Jordan_inner_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : ℝ :=
  sSup { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, A ⊆ E ∧ m = hA.measure }

noncomputable abbrev Jordan_outer_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : ℝ :=
  sInf { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, E ⊆ A ∧ m = hA.measure }

/-- Definition 1.1.4, extended to unbounded sets.  Exercise 1.2.5 of the text asks for the Jordan
inner measure "extended to unbounded sets in the obvious manner".  Because
{name}`Jordan_inner_measure` is real-valued, its supremum returns the junk value zero whenever the
elementary subsets of a set have unbounded measure, as happens for the whole space; this variant
takes the supremum in {name}`EReal` instead, so that such a set receives the value infinity.  The
two agree on bounded sets, by Jordan_inner_measure'_eq_coe below. -/
noncomputable abbrev Jordan_inner_measure' {d:ℕ} (E: Set (EuclideanSpace' d)) : EReal :=
  sSup { m:EReal | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A,
    A ⊆ E ∧ m = (hA.measure:EReal) }

/-- A bounded set is Jordan measurable if its inner and outer Jordan measures coincide. -/
noncomputable abbrev JordanMeasurable {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop :=
  Bornology.IsBounded E ∧ Jordan_inner_measure E = Jordan_outer_measure E

/-- The Jordan measure of a Jordan measurable set (equals both inner and outer measure). -/
noncomputable abbrev JordanMeasurable.measure {d:ℕ} {E: Set (EuclideanSpace' d)} (_: JordanMeasurable E) : ℝ :=
  Jordan_inner_measure E

