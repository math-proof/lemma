import Mathlib
import Def.Analysis.Misc.erdos_613.Part8
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

/-- {name}`redBlock1` is exactly the disjoint union of its {name}`A1` and {name}`B1` parts. -/
lemma redBlock1_eq_union (color : Sym2 V → Fin 2) :
  redBlock1 color =
    redBlock1A1 color ∪ redBlock1B1 color := by
  ext v; constructor
  · intro hv
    rcases Finset.mem_filter.1 hv with ⟨hRN, hB⟩
    have : isA1 v ∨ isB1 v := (inBlock1_iff v).1 hB
    cases this with
    | inl hA1 => exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨hRN, hA1⟩))
    | inr hB1 => exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨hRN, hB1⟩))
  · intro hv
    rcases Finset.mem_union.1 hv with hA1 | hB1
    · rcases Finset.mem_filter.1 hA1 with ⟨hRN, hA1⟩
      exact Finset.mem_filter.2 ⟨hRN, (inBlock1_iff v).2 (Or.inl hA1)⟩
    · rcases Finset.mem_filter.1 hB1 with ⟨hRN, hB1⟩
      exact Finset.mem_filter.2 ⟨hRN, (inBlock1_iff v).2 (Or.inr hB1)⟩

/-- {name}`redBlock2` is exactly the disjoint union of its {name}`A2` and {name}`B2` parts. -/
lemma redBlock2_eq_union (color : Sym2 V → Fin 2) :
  redBlock2 color =
    redBlock2A2 color ∪ redBlock2B2 color := by
  ext v; constructor
  · intro hv
    rcases Finset.mem_filter.1 hv with ⟨hRN, hB⟩
    have : isA2 v ∨ isB2 v := by
      apply (inBlock2_iff v).1
      cases v <;> simp_all [inBlock1, inBlock2, redNeighbors]

    cases this with
    | inl hA2 => exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨hRN, hA2⟩))
    | inr hB2 => exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨hRN, hB2⟩))
  · intro hv
    rcases Finset.mem_union.1 hv with hA2 | hB2
    · rcases Finset.mem_filter.1 hA2 with ⟨hRN, hA2⟩
      exact Finset.mem_filter.2 ⟨hRN, by
        cases v <;> simp_all [inBlock1, isA2]
        ⟩
    · rcases Finset.mem_filter.1 hB2 with ⟨hRN, hB2⟩
      exact Finset.mem_filter.2 ⟨hRN, by
        cases v <;> simp_all [inBlock1, isB2]⟩

/-- The two parts of {name}`redBlock1` are disjoint. -/
lemma redA1_redB1_disjoint (color : Sym2 V → Fin 2) :
  Disjoint (redBlock1A1 color) (redBlock1B1 color) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro v hvA hvB
  rcases Finset.mem_filter.1 hvA with ⟨_, hA1⟩
  rcases Finset.mem_filter.1 hvB with ⟨_, hB1⟩
  exact (not_isA1_and_isB1 v) ⟨hA1, hB1⟩

/-- The two parts of {name}`redBlock2` are disjoint. -/
lemma redA2_redB2_disjoint (color : Sym2 V → Fin 2) :
  Disjoint (redBlock2A2 color) (redBlock2B2 color) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro v hvA hvB
  rcases Finset.mem_filter.1 hvA with ⟨_, hA2⟩
  rcases Finset.mem_filter.1 hvB with ⟨_, hB2⟩
  exact (not_isA2_and_isB2 v) ⟨hA2, hB2⟩

/-- Cardinal decompositions of the blocks. -/
lemma redBlock1_card_eq_sum (color : Sym2 V → Fin 2) :
  (redBlock1 color).card
    = (redBlock1A1 color).card + (redBlock1B1 color).card := by
  classical
  have := Finset.card_union_add_card_inter
            (s := redBlock1A1 color) (t := redBlock1B1 color)
  -- rewrite the union as `redBlock1` and show the intersection is empty
  have hU : redBlock1A1 color ∪ redBlock1B1 color = redBlock1 color := by
    rw [redBlock1_eq_union]
  have hI : (redBlock1A1 color ∩ redBlock1B1 color).card = 0 := by
    have hdis := redA1_redB1_disjoint color
    -- `disjoint` implies the intersection is empty
    have : redBlock1A1 color ∩ redBlock1B1 color = (∅ : Finset V) := by
      simp [Disjoint] at hdis
      aesop
    aesop
  -- put it together
  have := by simpa [hU, hI, add_comm] using this
  exact this

lemma redBlock2_card_eq_sum (color : Sym2 V → Fin 2) :
  (redBlock2 color).card
    = (redBlock2A2 color).card + (redBlock2B2 color).card := by
  classical
  have := Finset.card_union_add_card_inter
            (s := redBlock2A2 color) (t := redBlock2B2 color)
  have hU : redBlock2A2 color ∪ redBlock2B2 color = redBlock2 color := by
    rw [redBlock2_eq_union]
  have hdis := redA2_redB2_disjoint color
  have hI : (redBlock2A2 color ∩ redBlock2B2 color).card = 0 := by
    have : redBlock2A2 color ∩ redBlock2B2 color = (∅ : Finset V) := by
      simp [Disjoint] at hdis
      aesop
    simp [this]
  have := by simpa [hU, hI, add_comm] using this
  exact this

end PikhurkoN5
