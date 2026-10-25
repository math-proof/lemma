import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Macro.Analysis.MeasureTheory.Section_1_1_1.Part2
open BoundedInterval


/-- Helper lemma: If a box is empty, its volume is zero -/
lemma Box.volume_eq_zero_of_empty {d:ℕ} (B: Box d) (h: B.toSet = ∅) : |B|ᵥ = 0 := by
  -- If B.toSet = ∅, then the box has at least one empty side interval
  have : ∃ i, (B.side i).toSet = ∅ := by
    by_contra! h_all_nonempty
    have h_all_nonempty : ∀ i, (B.side i).toSet.Nonempty := h_all_nonempty
    choose x hx using h_all_nonempty
    have h_nonempty : B.toSet.Nonempty := ⟨.toLp 2 (fun i ↦ x i), by simp; exact fun i => hx i⟩
    rw [h] at h_nonempty
    exact Set.not_nonempty_empty h_nonempty
  obtain ⟨i, hi⟩ := this
  -- Show |B.side i|ₗ = 0, which implies |B|ᵥ = 0
  rw [Box.volume]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  -- If (B.side i).toSet = ∅, then the interval is degenerate (b ≤ a), so length = 0
  have h_le : (B.side i).b ≤ (B.side i).a := by
    match B.side i, hi with
    | Ioo a b, hi => simp [BoundedInterval.set_Ioo] at hi; simp; exact le_of_not_gt (Set.Ioo_eq_empty_iff.1 hi)
    | Icc a b, hi => simp [BoundedInterval.set_Icc] at hi; simp; exact le_of_not_ge (Set.Icc_eq_empty_iff.1 hi)
    | Ioc a b, hi => simp [BoundedInterval.set_Ioc] at hi; simp; exact le_of_not_gt (Set.Ioc_eq_empty_iff.1 hi)
    | Ico a b, hi => simp [BoundedInterval.set_Ico] at hi; simp; exact le_of_not_gt (Set.Ico_eq_empty_iff.1 hi)
  simp [BoundedInterval.length, max_eq_right (sub_nonpos.2 h_le)]

/-- A box with all degenerate sides \[x, x\] has volume 0 when d > 0 -/
lemma Box.volume_singleton {d:ℕ} (hd : 0 < d) (x : EuclideanSpace' d) :
    |⟨fun i => BoundedInterval.Icc (x i) (x i)⟩|ᵥ = 0 := by
  unfold Box.volume BoundedInterval.length
  -- All sides have length 0
  have h_sides : ∀ i : Fin d, max ((x i) - (x i)) 0 = 0 := by
    intro i
    simp [sub_self]
  -- Product contains at least one 0 (at index 0), so the product is 0
  let i₀ : Fin d := ⟨0, hd⟩
  calc ∏ i : Fin d, max ((x i) - (x i)) 0
      = ∏ i : Fin d, (0 : ℝ) := by simp only [h_sides]
    _ = 0 := Finset.prod_eq_zero (Finset.mem_univ i₀) rfl

/-- A nonempty box has nonempty sides at each dimension -/
lemma Box.side_nonempty_of_nonempty {d:ℕ} (B : Box d) (hB : B.toSet.Nonempty) (i : Fin d) :
    (B.side i).toSet.Nonempty := by
  obtain ⟨f, hf⟩ := hB
  simp at hf
  exact ⟨f i, hf i⟩

/-- The volume of a 1D box equals the length of the underlying interval. -/
@[simp]
theorem Box.volume_of_interval (I:BoundedInterval) : |(I:Box 1)|ᵥ = |I|ₗ := by
  simp [Box.volume]

/-- {name}`Box.toSet` is injective on non-empty boxes -/
lemma Box.toSet_injective_of_nonempty {d:ℕ} {B₁ B₂ : Box d}
    (h₁ : B₁.toSet.Nonempty) (h₂ : B₂.toSet.Nonempty) (h_eq : B₁.toSet = B₂.toSet) :
    B₁ = B₂ := by
  -- Use Box extensionality: boxes are equal if their sides are equal
  ext i
  -- From B₁.toSet = B₂.toSet, extract that B₁.side i = B₂.side i
  -- B.toSet = Set.univ.pi (fun i => (B.side i).toSet)
  -- So if the pi sets are equal, each coordinate set must be equal
  have h_side : (B₁.side i).toSet = (B₂.side i).toSet := by
    -- Use Set extensionality: show x ∈ B₁.side i ↔ x ∈ B₂.side i for all x
    ext x
    -- Get a witness function from the nonempty hypothesis
    obtain ⟨f, hf⟩ := h₁
    simp at hf
    -- Construct a test function that equals x at coordinate i, and equals f elsewhere
    let g : EuclideanSpace' d := .toLp 2 (fun j => if j = i then x else f j)
    -- Show: x ∈ B₁.side i ↔ x ∈ B₂.side i
    constructor
    · intro hx
      have hg₁ : g ∈ B₁.toSet := by
        simp [g]
        intro j
        by_cases h : j = i
        · simp [h, hx]
        · simp [h, hf j]
      rw [h_eq] at hg₁
      simp at hg₁
      have := hg₁ i
      simp [g] at this
      exact this
    · intro hx
      obtain ⟨f₂, hf₂⟩ := h₂
      simp at hf₂
      let g₂ : EuclideanSpace' d := .toLp 2 (fun j => if j = i then x else f₂ j)
      have hg₂ : g₂ ∈ B₂.toSet := by
        simp [g₂]
        intro j
        by_cases h : j = i
        · simp [h, hx]
        · simp [h, hf₂ j]
      rw [← h_eq] at hg₂
      simp at hg₂
      have := hg₂ i
      simp [g₂] at this
      exact this
  -- Now use BoundedInterval injectivity
  have h_sides_nonempty : (B₁.side i).toSet.Nonempty ∧ (B₂.side i).toSet.Nonempty := by
    constructor
    · obtain ⟨f, hf⟩ := h₁
      simp at hf
      exact ⟨f i, hf i⟩
    · obtain ⟨f, hf⟩ := h₂
      simp at hf
      exact ⟨f i, hf i⟩
  exact BoundedInterval.toSet_injective_of_nonempty h_sides_nonempty.1 h_sides_nonempty.2 h_side

