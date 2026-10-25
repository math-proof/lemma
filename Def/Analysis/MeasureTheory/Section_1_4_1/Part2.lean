import Mathlib.Order.BooleanAlgebra.Defs
import Def.Analysis.MeasureTheory.Section_1_3_5.Part3
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part2


def JordanMeasurable.gt_elementary_boolean_algebra (d:ℕ) :
  JordanMeasurable.boolean_algebra d ≥ EuclideanSpace'.elementary_boolean_algebra d := by
  intro E hE
  rcases hE with h | h
  · exact Or.inl h.jordanMeasurable
  · exact Or.inr h.jordanMeasurable

/-- Example 1.4.5 (Lebesgue algebra) -/
def LebesgueMeasurable.boolean_algebra (d:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  {
    measurable := fun E => LebesgueMeasurable E
    empty_mem := LebesgueMeasurable.empty
    compl_mem := fun _ hE => hE.complement
    union_mem := fun _ _ hE hF => hE.union hF
  }

def LebesgueMeasurable.gt_jordan_boolean_algebra (d:ℕ) :
  LebesgueMeasurable.boolean_algebra d ≥ JordanMeasurable.boolean_algebra d := by
  intro E hE
  rcases hE with h | h
  · exact Jordan_measurable.lebesgue h
  · have hL : LebesgueMeasurable Eᶜᶜ := (Jordan_measurable.lebesgue h).complement
    rw [compl_compl] at hL
    exact hL

/-- Example 1.4.6 (Null algebra) -/
def IsNull.boolean_algebra (d:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  {
    measurable := fun E => IsNull E ∨ IsNull Eᶜ
    empty_mem := Or.inl Lebesgue_measure.empty
    compl_mem := fun E hE => by simpa only [compl_compl] using hE.symm
    union_mem := fun E F hE hF => by
      rcases hE with hE | hE <;> rcases hF with hF | hF
      · refine Or.inl ?_
        have hle : Lebesgue_outer_measure (E ∪ F) ≤
            Lebesgue_outer_measure E + Lebesgue_outer_measure F := by
          have h_union : (⋃ i : Fin 2, if i = 0 then E else F) = E ∪ F := by
            ext x
            simp [Fin.exists_fin_two]
          simpa [h_union, Fin.sum_univ_two] using
            Lebesgue_outer_measure.finite_union_le (fun i : Fin 2 => if i = 0 then E else F)
        simp [hE, hF] at hle
        exact le_antisymm hle (Lebesgue_outer_measure.nonneg _)
      · refine Or.inr (IsNull.subset hF ?_)
        intro x hx
        exact fun h => hx (Or.inr h)
      · refine Or.inr (IsNull.subset hE ?_)
        intro x hx
        exact fun h => hx (Or.inl h)
      · refine Or.inr (IsNull.subset hE ?_)
        intro x hx
        exact fun h => hx (Or.inl h)
  }

def IsNull.lt_lebesgue_boolean_algebra (d:ℕ) :
  IsNull.boolean_algebra d ≤ LebesgueMeasurable.boolean_algebra d := by
  intro E hE
  rcases hE with h | h
  · exact IsNull.measurable h
  · have hL : LebesgueMeasurable Eᶜᶜ := (IsNull.measurable h).complement
    rw [compl_compl] at hL
    exact hL

/-- Exercise 1.4.2 (Restriction) -/
def ConcreteBooleanAlgebra.restrict {X:Type*} (B: ConcreteBooleanAlgebra X) (A:Set X) : ConcreteBooleanAlgebra A :=
  {
    measurable := fun E => ∃ E' : Set X, B.measurable E' ∧ E = Subtype.val ⁻¹' E'
    empty_mem := ⟨∅, B.empty_mem, by simp⟩
    compl_mem := fun E ⟨E', hE', hE⟩ =>
      ⟨E'ᶜ, B.compl_mem E' hE', by simp [hE]⟩
    union_mem := fun E F ⟨E', hE', hE⟩ ⟨F', hF', hF⟩ =>
      ⟨E' ∪ F', B.union_mem E' F' hE' hF', by simp [hE, hF]⟩
  }

def IsPartition {I X:Type*} (parts: I → Set X) : Prop := (Set.PairwiseDisjoint Set.univ parts) ∧ (⋃ i, parts i = Set.univ)

def IsPartition.discrete (X:Type*) : IsPartition (fun x:X ↦ {x}) := by
  refine ⟨?_, ?_⟩
  · intro x _ y _ hxy
    exact Set.disjoint_singleton.mpr hxy
  · ext x
    simp [Set.mem_iUnion]

def IsPartition.trivial (X:Type*) : IsPartition (fun (x:Unit) ↦ (Set.univ: Set X)) := by
  refine ⟨?_, ?_⟩
  · intro a _ b _ hne
    exact (hne (Subsingleton.elim a b)).elim
  · ext x
    constructor
    · intro _
      trivial
    · intro _
      exact Set.mem_iUnion.mpr ⟨(), Set.mem_univ x⟩

def IsPartition.finer_than {I J X:Type*} {parts_I: I → Set X} {parts_J: J → Set X}
  (_: IsPartition parts_I) (_: IsPartition parts_J) : Prop :=
  ∀ i:I, ∃ j:J, parts_I i ⊆ parts_J j

/-- A variant of {name}`DyadicCube` with {name}`BoundedInterval.Ico` intervals -/
noncomputable def DyadicCube' {d:ℕ} (n:ℤ) (a: Fin d → ℤ) : Box d := { side := fun i ↦ BoundedInterval.Ico (a i/2^n) ((a i + 1)/2^n) }

def DyadicCube'.boolean_algebra (d n:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  (DyadicCube'.partition d n).to_ConcreteBooleanAlgebra

def IsPartition.relabels {I J X:Type*} {parts_I: I → Set X} (_: IsPartition parts_I) {parts_J : J → Set X} (_: IsPartition parts_J) : Prop := ∃ e : I ≃ J, ∀ i:I, parts_I i = parts_J (e i)

def IsPartition.no_empty {I X:Type*} {parts: I → Set X} (_: IsPartition parts) : Prop := ∀ i:I, parts i ≠ ∅

def ConcreteBooleanAlgebra.isAtomic {X:Type*} (B: ConcreteBooleanAlgebra X) : Prop :=
  ∃ (I:Type*) (parts: I → Set X) (hI:IsPartition parts), B = hI.to_ConcreteBooleanAlgebra

