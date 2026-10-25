import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Abbrev.Analysis.MeasureTheory.Section_1_1_1.Part5
open BoundedInterval


/-- Every box is an elementary set (witnessed by the singleton finset). -/
theorem IsElementary.box {d:ℕ} (B: Box d) : IsElementary B.toSet := by
  use {B}
  simp

/-- Exercise 1.1.1 (Boolean closure): The union of two elementary sets is elementary. -/
theorem IsElementary.union {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E ∪ F) := by
  classical
  obtain ⟨S, rfl⟩ := hE
  obtain ⟨T, rfl⟩ := hF
  exact ⟨S ∪ T, (Finset.set_biUnion_union S T _).symm⟩

/-- The empty set is elementary. -/
theorem IsElementary.empty (d:ℕ) : IsElementary (∅: Set (EuclideanSpace' d)) := by
  exact ⟨∅, by simp⟩

/-- The union of a finset of elementary sets is elementary. -/
lemma IsElementary.union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, IsElementary E) : IsElementary (⋃ E ∈ S, E) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using IsElementary.empty d
  | insert a S' ha ih =>
    have hrest : IsElementary (⋃ E ∈ S', E) :=
      ih (fun E hE' ↦ hE E (Finset.mem_insert_of_mem hE'))
    have ha' : IsElementary a := hE a (Finset.mem_insert_self a S')
    simpa using ha'.union hrest

/-- The intersection of two boxes is a box: intersect the sides coordinatewise. -/
lemma Box.inter {d:ℕ} (B₁ B₂ : Box d) :
    ∃ B : Box d, B.toSet = B₁.toSet ∩ B₂.toSet := by
  refine ⟨⟨fun i ↦ B₁.side i ∩ B₂.side i⟩, ?_⟩
  ext x
  simp only [Box.mem_toSet, Set.mem_inter_iff]
  constructor
  · intro hx
    exact ⟨fun i ↦ ((BoundedInterval.inter_eq _ _ ▸ hx i : x i ∈ (B₁.side i:Set ℝ) ∩ _)).1,
           fun i ↦ ((BoundedInterval.inter_eq _ _ ▸ hx i : x i ∈ (B₁.side i:Set ℝ) ∩ _)).2⟩
  · intro ⟨h₁, h₂⟩ i
    have : x i ∈ (B₁.side i:Set ℝ) ∩ (B₂.side i:Set ℝ) := ⟨h₁ i, h₂ i⟩
    rwa [← BoundedInterval.inter_eq] at this

/-- Exercise 1.1.1 (Boolean closure): The intersection of two elementary sets is elementary. -/
theorem IsElementary.inter {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E ∩ F) := by
  classical
  obtain ⟨S, rfl⟩ := hE
  obtain ⟨T, rfl⟩ := hF
  choose f hf using fun p : Box d × Box d ↦ Box.inter p.1 p.2
  refine ⟨(S ×ˢ T).image f, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨B, hB, hxB⟩, ⟨C, hC, hxC⟩⟩
    refine ⟨f (B, C), ⟨⟨(B, C), ⟨hB, hC⟩, rfl⟩, ?_⟩⟩
    rw [hf (B, C)]
    exact ⟨hxB, hxC⟩
  · rintro ⟨D, ⟨⟨⟨B, C⟩, ⟨hB, hC⟩, rfl⟩, hxD⟩⟩
    rw [hf (B, C)] at hxD
    exact ⟨⟨B, hB, hxD.1⟩, ⟨C, hC, hxD.2⟩⟩

