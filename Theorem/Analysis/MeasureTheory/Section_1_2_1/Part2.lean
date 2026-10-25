import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Def.Analysis.MeasureTheory.Section_1_2_1
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


namespace BoundedInterval

/-- The left half of bisection has half the original length -/
lemma bisect_fst_length (I : BoundedInterval) :
    |(I.bisect.fst)|ₗ = |I|ₗ / 2 := by
  unfold bisect midpoint endpoints length
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    -- Goal: max ((a + b) / 2 - a) 0 = max (b - a) 0 / 2
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Icc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ioc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ico a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]

/-- The right half of bisection has half the original length -/
lemma bisect_snd_length (I : BoundedInterval) :
    |(I.bisect.snd)|ₗ = |I|ₗ / 2 := by
  unfold bisect midpoint endpoints length
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    -- Goal: max (b - (a + b) / 2) 0 = max (b - a) 0 / 2
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Icc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ioc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ico a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]

/-- Bisecting preserves total length -/
lemma bisect_length_sum (I : BoundedInterval) :
    |(I.bisect.fst)|ₗ + |(I.bisect.snd)|ₗ = |I|ₗ := by
  rw [bisect_fst_length, bisect_snd_length]
  ring

/-- The left endpoint of bisect.fst is I.a -/
@[simp]
lemma bisect_fst_a (I : BoundedInterval) : (I.bisect.fst).a = I.a := by
  unfold bisect endpoints
  cases I <;> simp [BoundedInterval.a]

/-- The left endpoint of bisect.snd is I.midpoint -/
@[simp]
lemma bisect_snd_a (I : BoundedInterval) : (I.bisect.snd).a = I.midpoint := by
  unfold bisect endpoints
  cases I <;> simp [BoundedInterval.a, midpoint]

/-- The midpoint equals a + length/2 when a ≤ b (non-degenerate interval) -/
lemma midpoint_eq_a_add_half_length (I : BoundedInterval) (h : I.a ≤ I.b) :
    I.midpoint = I.a + |I|ₗ / 2 := by
  unfold midpoint endpoints length
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring
  | Icc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring
  | Ioc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring
  | Ico a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring

/-- The midpoint is in the first half of bisection (as the right endpoint of {name}`BoundedInterval.Icc`) -/
lemma midpoint_mem_bisect_fst (I : BoundedInterval) (h : I.toSet.Nonempty) :
    I.midpoint ∈ (I.bisect.fst).toSet := by
  obtain ⟨x, hx⟩ := h
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩

/-- The midpoint is in the second half of bisection (as the left endpoint of {name}`BoundedInterval.Icc`) -/
lemma midpoint_mem_bisect_snd (I : BoundedInterval) (h : I.toSet.Nonempty) :
    I.midpoint ∈ (I.bisect.snd).toSet := by
  obtain ⟨x, hx⟩ := h
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩

/-- A point is in I.bisect.snd iff it's in I.toSet and at or above the midpoint -/
lemma mem_bisect_snd_iff (I : BoundedInterval) (x : ℝ) (hx : x ∈ I.toSet) :
    x ∈ (I.bisect.snd).toSet ↔ x ≥ I.midpoint := by
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩

/-- A point is in I.bisect.fst iff it's in I.toSet and below the midpoint -/
lemma mem_bisect_fst_iff (I : BoundedInterval) (x : ℝ) (hx : x ∈ I.toSet) :
    x ∈ (I.bisect.fst).toSet ↔ x ≤ I.midpoint := by
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩

/-- If two intervals have equal bisect.fst, then their endpoints match -/
lemma bisect_fst_eq_endpoints {I₁ I₂ : BoundedInterval}
    (h : I₁.bisect.fst = I₂.bisect.fst) : I₁.a = I₂.a ∧ I₁.b = I₂.b := by
  -- bisect.fst = Icc I.a I.midpoint, so (bisect.fst).a = I.a
  have ha' : (I₁.bisect.fst).a = (I₂.bisect.fst).a := congrArg (·.a) h
  have hm' : (I₁.bisect.fst).b = (I₂.bisect.fst).b := congrArg (·.b) h
  simp only [bisect, endpoints, midpoint, BoundedInterval.a, BoundedInterval.b] at ha' hm'
  constructor
  · cases I₁ <;> cases I₂ <;> simp_all
  · cases I₁ <;> cases I₂ <;> simp only [BoundedInterval.b] at ha' hm' ⊢ <;> linarith

/-- If two intervals have equal bisect.snd, then their endpoints match -/
lemma bisect_snd_eq_endpoints {I₁ I₂ : BoundedInterval}
    (h : I₁.bisect.snd = I₂.bisect.snd) : I₁.a = I₂.a ∧ I₁.b = I₂.b := by
  -- bisect.snd = Icc midpoint b, so (bisect.snd).a = midpoint and (bisect.snd).b = b
  have hm' : (I₁.bisect.snd).a = (I₂.bisect.snd).a := congrArg (·.a) h
  have hb' : (I₁.bisect.snd).b = (I₂.bisect.snd).b := congrArg (·.b) h
  -- The .b of bisect.snd is just I.b, and .a is (I.a + I.b)/2
  cases I₁ with | _ a₁ b₁ =>
  cases I₂ with | _ a₂ b₂ =>
  all_goals simp only [bisect, endpoints, midpoint, BoundedInterval.a, BoundedInterval.b] at hm' hb' ⊢
  -- Now hm' : (a₁ + b₁)/2 = (a₂ + b₂)/2 and hb' : b₁ = b₂
  all_goals constructor <;> linarith

/-- Cross-case: if bisect.fst = bisect.snd, the intervals have overlapping midpoint and endpoint -/
lemma bisect_fst_eq_snd_shift {I₁ I₂ : BoundedInterval}
    (h : I₁.bisect.fst = I₂.bisect.snd) : I₁.a = (I₂.a + I₂.b) / 2 := by
  -- (bisect.fst).a = I.a, (bisect.snd).a = I.midpoint = (I.a + I.b)/2
  have ha' : (I₁.bisect.fst).a = (I₂.bisect.snd).a := congrArg (·.a) h
  cases I₁ with | _ a₁ b₁ =>
  cases I₂ with | _ a₂ b₂ =>
  all_goals simp only [bisect, endpoints, midpoint, BoundedInterval.a, BoundedInterval.b] at ha' ⊢
  all_goals linarith

end BoundedInterval
