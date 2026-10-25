import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
import Theorem.Analysis.MeasureTheory.Section_1_2_2.Part3
  IsOpen.measurable isOpen_empty

  intro ε hε
  use ∅
  constructor
  · exact isOpen_empty
  constructor
  · exact Set.empty_subset ∅
  · have h_empty : ∅ \ ∅ = (∅ : Set (EuclideanSpace' d)) := Set.diff_self
    rw [h_empty]
    rw [Lebesgue_outer_measure.of_empty d]
    exact le_of_lt hε

open BoundedInterval


noncomputable def inner_measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : ℝ := (Lebesgue_measure hE.inElementary.choose).toReal - (Lebesgue_measure (hE.inElementary.choose \ E)).toReal

def IsFσ  {X:Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsClosed t) ∧ T.Countable ∧ s = ⋃₀ T

open Pointwise

def IsElementary.ae_subsets {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) := Quotient hA.ae_equiv

def IsElementary.ae_quot {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: Set A): hA.ae_subsets := Quotient.mk' (s := hA.ae_equiv) E

noncomputable def IsElementary.ae_elem {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : Set hA.ae_subsets := { E | ∃ F: Set A, IsElementary (Subtype.val '' F) ∧ hA.ae_quot F = E }

noncomputable def IsElementary.ae_measurable {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : Set hA.ae_subsets := { E | ∃ F: Set A, LebesgueMeasurable (Subtype.val '' F) ∧ hA.ae_quot F = E }

noncomputable def IsElementary.ae_measure {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: hA.ae_measurable) : ℝ := (Lebesgue_measure (Subtype.val '' E.property.choose)).toReal

noncomputable def IsElementary.ae_elem_measure {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: hA.ae_elem) : ℝ := E.property.choose_spec.1.measure

