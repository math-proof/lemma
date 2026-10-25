import Abbrev.Analysis.MeasureTheory.Section_1_2_2.Part3
import Abbrev.Analysis.MeasureTheory.Section_1_2_3
open scoped Pointwise

/-!
# Introduction to Measure Theory, Section 1.2.3: Non-measurable sets

A companion to (the introduction to) Section 1.2.3 of the book "An introduction to Measure Theory".

-/


/-- ℚ is dense in ℝ, so every coset of ℝ/ℚ intersects \[0,1\] -/
lemma coset_intersects_unit_interval (c : RealModRat) :
    ∃ x : ℝ, x ∈ Set.Icc 0 1 ∧ QuotientAddGroup.mk (s := Rat.addSubgroup) x = c := by
  obtain ⟨r⟩ := c
  -- r is a representative of the coset c
  -- By density of ℚ, find q ∈ ℚ such that r - q ∈ [0,1]
  have hdense : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.isDenseEmbedding_coe_real.dense
  -- The set {r - t : t ∈ (0,1)} is open and nonempty, so contains a rational
  have h_open : IsOpen (Set.Ioo (r - 1) r) := isOpen_Ioo
  have h_nonempty : Set.Nonempty (Set.Ioo (r - 1) r) := by
    use r - 1/2; constructor <;> linarith
  obtain ⟨q_real, ⟨hq_rat, hq_in⟩⟩ := hdense.exists_mem_open h_open h_nonempty
  obtain ⟨q, rfl⟩ := hq_rat
  use r - q
  constructor
  · constructor
    · linarith [hq_in.2]
    · linarith [hq_in.1]
  · -- r - q is in the same coset as r
    show QuotientAddGroup.mk (s := Rat.addSubgroup) (r - (q : ℝ)) =
         Quot.mk (QuotientAddGroup.leftRel Rat.addSubgroup) r
    have heq : (QuotientAddGroup.mk (s := Rat.addSubgroup) (r - (q : ℝ))) =
           (QuotientAddGroup.mk (s := Rat.addSubgroup) r) := by
      rw [QuotientAddGroup.eq]
      -- Need to show: -(r - q) + r ∈ Rat.addSubgroup
      -- That is: q ∈ Rat.addSubgroup
      show -(r - ↑q) + r ∈ Rat.addSubgroup
      simp only [neg_sub, sub_add_cancel]
      exact ⟨q, rfl⟩
    rw [heq]
    rfl

