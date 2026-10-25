import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Def.Analysis.MeasureTheory.Section_1_2_1.Part4
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


namespace Box

lemma subdivide_iter_zero {d:ℕ} (B: Box d) : subdivide_iter B 0 = {B} := rfl

lemma subdivide_iter_succ {d:ℕ} (B: Box d) (k: ℕ) :
    subdivide_iter B (k+1) = (subdivide_iter B k).biUnion Box.subdivide := rfl

/-- All sides in {name}`Box.subdivide` (single level) are {name}`BoundedInterval.Icc` intervals -/
lemma subdivide_side_is_Icc {d:ℕ} (B: Box d) (B' : Box d) (hB' : B' ∈ B.subdivide) (i : Fin d) :
    ∃ a b, B'.side i = Icc a b := by
  simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hB'
  obtain ⟨c, rfl⟩ := hB'
  -- B' = { side := fun j => if c j then ... else ... }
  -- B'.side i = if c i then (B.side i).bisect.snd else (B.side i).bisect.fst
  simp only  -- This introduces the if-then-else in the goal
  split_ifs with hc
  · -- snd case: (B.side i).bisect.snd is Icc
    unfold BoundedInterval.bisect BoundedInterval.endpoints BoundedInterval.midpoint
    cases B.side i <;> exact ⟨_, _, rfl⟩
  · -- fst case: (B.side i).bisect.fst is Icc
    unfold BoundedInterval.bisect BoundedInterval.endpoints BoundedInterval.midpoint
    cases B.side i <;> exact ⟨_, _, rfl⟩

/-- All sides in {name}`Box.subdivide_iter` for k ≥ 1 are {name}`BoundedInterval.Icc` intervals -/
lemma subdivide_iter_side_is_Icc {d:ℕ} (B: Box d) (k : ℕ) (B' : Box d)
    (hB' : B' ∈ subdivide_iter B (k+1)) (i : Fin d) :
    ∃ a b, B'.side i = Icc a b := by
  induction k generalizing B' with
  | zero =>
    simp only [subdivide_iter, Finset.mem_biUnion, Finset.mem_singleton] at hB'
    obtain ⟨B'', rfl, hB'_sub⟩ := hB'
    exact subdivide_side_is_Icc B'' B' hB'_sub i
  | succ k ih =>
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB'', hB'_sub⟩ := hB'
    exact subdivide_side_is_Icc B'' B' hB'_sub i

/-- All boxes in {name}`Box.subdivide_iter` have the same side lengths at each coordinate -/
lemma subdivide_iter_side_length {d:ℕ} (B : Box d) (k : ℕ) (B' : Box d)
    (hB' : B' ∈ subdivide_iter B k) (i : Fin d) :
    |B'.side i|ₗ = |B.side i|ₗ / 2^k := by
  induction k generalizing B' with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton] at hB'
    simp [hB']
  | succ k ih =>
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB'', hB'_sub⟩ := hB'
    have h1 := ih B'' hB''
    simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hB'_sub
    obtain ⟨c, rfl⟩ := hB'_sub
    simp only
    split_ifs with hc
    · rw [BoundedInterval.bisect_snd_length, h1]; ring
    · rw [BoundedInterval.bisect_fst_length, h1]; ring

/-- A nonempty box remains nonempty after subdivision -/
lemma subdivide_one_step_nonempty {d:ℕ} (B: Box d) (hB: B.toSet.Nonempty) :
    ∀ B' ∈ B.subdivide, B'.toSet.Nonempty := by
  intro B' hB'
  unfold subdivide at hB'
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hB'
  obtain ⟨choice, rfl⟩ := hB'
  -- The midpoint of B is in all sub-boxes
  use .toLp 2 (fun i => (B.side i).midpoint)
  intro i
  have h_side_nonempty : (B.side i).toSet.Nonempty := by
    obtain ⟨x, hx⟩ := hB
    exact ⟨x i, hx i⟩
  simp only
  split_ifs with h
  · exact BoundedInterval.midpoint_mem_bisect_snd (B.side i) h_side_nonempty
  · exact BoundedInterval.midpoint_mem_bisect_fst (B.side i) h_side_nonempty

/-- A nonempty box remains nonempty after k iterations of subdivision -/
lemma subdivide_iter_nonempty {d:ℕ} (B: Box d) (hB: B.toSet.Nonempty) (k: ℕ) :
    ∀ B' ∈ subdivide_iter B k, B'.toSet.Nonempty := by
  induction k with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton]
    intro B' hB'; rw [hB']; exact hB
  | succ k ih =>
    intro B' hB'
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB''_mem, hB'_sub⟩ := hB'
    exact subdivide_one_step_nonempty B'' (ih B'' hB''_mem) B' hB'_sub

/-- Grid alignment: sides in {name}`Box.subdivide_iter` start at grid positions.
    Requires nonempty box to ensure sides have a ≤ b (backwards intervals break the formula). -/
lemma subdivide_iter_side_grid {d:ℕ} (B : Box d) (hB : B.toSet.Nonempty) (k : ℕ) (B' : Box d)
    (hB' : B' ∈ subdivide_iter B k) (i : Fin d) :
    ∃ j : ℕ, j < 2^k ∧ (B'.side i).a = (B.side i).a + j * (|B.side i|ₗ / 2^k) := by
  induction k generalizing B' with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton] at hB'
    use 0
    simp [hB']
  | succ k ih =>
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB'', hB'_sub⟩ := hB'
    obtain ⟨j'', hj''_bound, hj''_eq⟩ := ih B'' hB''
    simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hB'_sub
    obtain ⟨c, rfl⟩ := hB'_sub
    have h_len := subdivide_iter_side_length B k B'' hB'' i
    simp only
    split_ifs with hc
    · -- snd case: start at midpoint of B''
      use 2 * j'' + 1
      constructor
      · omega
      · -- (bisect.snd).a = midpoint = B''.a + |B''|ₗ/2
        rw [BoundedInterval.bisect_snd_a]
        have h_B''_len : |B''.side i|ₗ = |B.side i|ₗ / 2 ^ k := h_len
        by_cases h_nondeg : (B''.side i).a ≤ (B''.side i).b
        · -- Non-degenerate: use midpoint_eq_a_add_half_length
          rw [BoundedInterval.midpoint_eq_a_add_half_length _ h_nondeg, hj''_eq, h_B''_len]
          have h2k : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
          rw [h2k]
          have h2k_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
          field_simp [h2k_ne]
          push_cast; ring
        · -- Degenerate case: impossible for nonempty boxes (all sides have a ≤ b)
          -- B'' is nonempty since B is nonempty
          have hB''_nonempty : B''.toSet.Nonempty := subdivide_iter_nonempty B hB k B'' hB''
          -- Therefore (B''.side i) is nonempty
          have h_side_nonempty : (B''.side i).toSet.Nonempty :=
            Box.side_nonempty_of_nonempty B'' hB''_nonempty i
          -- Nonempty intervals have a ≤ b
          have h_order : (B''.side i).a ≤ (B''.side i).b :=
            BoundedInterval.nonempty_implies_le _ h_side_nonempty
          -- Contradiction with ¬h_nondeg
          exact absurd h_order h_nondeg
    · -- fst case: start at B''.a (left endpoint preserved)
      use 2 * j''
      constructor
      · omega
      · rw [BoundedInterval.bisect_fst_a, hj''_eq]
        have h2k : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
        rw [h2k]
        have h2k_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
        field_simp [h2k_ne]
        push_cast; ring

/-- Volume is preserved through iterative subdivision -/
lemma volume_subdivide_iter {d:ℕ} (B: Box d) (hB : B.toSet.Nonempty) (k: ℕ) :
    ∑ B' ∈ subdivide_iter B k, |B'|ᵥ = |B|ᵥ := by
  induction k with
  | zero => simp [subdivide_iter]
  | succ k ih =>
    simp only [subdivide_iter_succ]
    rw [Finset.sum_biUnion]
    · -- Each inner sum ∑ i ∈ x.subdivide, |i|ᵥ = |x|ᵥ by volume_subdivide
      calc ∑ x ∈ subdivide_iter B k, ∑ i ∈ x.subdivide, |i|ᵥ
          = ∑ x ∈ subdivide_iter B k, |x|ᵥ := by
            apply Finset.sum_congr rfl
            intro B' _
            exact volume_subdivide B'
        _ = |B|ᵥ := ih
    · -- Pairwise disjointness of subdivisions from different parent boxes
      intro B₁ hB₁ B₂ hB₂ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_iff_ne]
      intro s₁ hs₁ s₂ hs₂
      -- Extract choice functions from membership in subdivide
      simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hs₁ hs₂
      obtain ⟨c₁, rfl⟩ := hs₁
      obtain ⟨c₂, rfl⟩ := hs₂
      -- Suppose for contradiction that s₁ = s₂
      intro heq
      apply hne
      -- Show B₁ = B₂ using Box.ext
      ext i
      -- At coordinate i, the sides of s₁ and s₂ must be equal
      have h_side_eq : (if c₁ i then (B₁.side i).bisect.snd else (B₁.side i).bisect.fst) =
                       (if c₂ i then (B₂.side i).bisect.snd else (B₂.side i).bisect.fst) := by
        have := congrFun (congrArg Box.side heq) i
        simpa using this
      -- At level k ≥ 1, all sides are Icc. k = 0 case: subdivide_iter B 0 = {B}, so B₁ = B₂
      match k with
      | 0 =>
        -- subdivide_iter B 0 = {B}, so B₁ = B and B₂ = B
        have hB₁' : B₁ = B := by simpa [subdivide_iter] using hB₁
        have hB₂' : B₂ = B := by simpa [subdivide_iter] using hB₂
        simp [hB₁', hB₂']
      | k'+1 =>
      -- Get Icc structure for both sides
      obtain ⟨a₁, b₁, h_side₁⟩ := subdivide_iter_side_is_Icc B k' B₁ hB₁ i
      obtain ⟨a₂, b₂, h_side₂⟩ := subdivide_iter_side_is_Icc B k' B₂ hB₂ i
      -- Get grid positions for B₁.side i and B₂.side i
      obtain ⟨j₁, _, hj₁⟩ := subdivide_iter_side_grid B hB (k'+1) B₁ hB₁ i
      obtain ⟨j₂, _, hj₂⟩ := subdivide_iter_side_grid B hB (k'+1) B₂ hB₂ i
      -- Both have the same length
      have h_len₁ := subdivide_iter_side_length B (k'+1) B₁ hB₁ i
      have h_len₂ := subdivide_iter_side_length B (k'+1) B₂ hB₂ i
      have h_same_len : |B₁.side i|ₗ = |B₂.side i|ₗ := by rw [h_len₁, h_len₂]
      -- Case analysis on c₁ i and c₂ i
      cases hc₁ : c₁ i <;> cases hc₂ : c₂ i <;> simp only [hc₁, hc₂, ite_true] at h_side_eq
      · -- fst = fst case: endpoint equality implies parent equality
        obtain ⟨ha, hb⟩ := BoundedInterval.bisect_fst_eq_endpoints h_side_eq
        -- Both sides are Icc with same endpoints
        simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at ha hb ⊢
        simp [ha, hb]
      · -- fst = snd cross case: parity contradiction via grid positions
        -- Key insight: Grid positions are integers, but fst=snd requires half-integer offset
        -- For degenerate case (L=0): all intervals collapse, so B₁=B₂
        by_cases hL : |B.side i|ₗ = 0
        · -- Degenerate case: all sides at dimension i are singletons
          -- When length = 0 for nonempty box, a = b (singleton)
          -- All subdivisions have same singleton side
          have h1a : (B₁.side i).a = (B.side i).a := by rw [hj₁, hL]; simp
          have h2a : (B₂.side i).a = (B.side i).a := by rw [hj₂, hL]; simp
          have h1len : |B₁.side i|ₗ = 0 := by rw [h_len₁, hL]; simp
          have h2len : |B₂.side i|ₗ = 0 := by rw [h_len₂, hL]; simp
          -- For nonempty Icc intervals with length 0: a = b
          have hB1_nonempty : B₁.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₁ hB₁
          have hB2_nonempty : B₂.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₂ hB₂
          have h1b : (B₁.side i).b = (B₁.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₁ hB1_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            -- For Icc a b, length 0 with a ≤ b means a = b
            unfold BoundedInterval.length at h1len
            simp only [max_eq_right_iff] at h1len
            linarith
          have h2b : (B₂.side i).b = (B₂.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₂ hB2_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            unfold BoundedInterval.length at h2len
            simp only [max_eq_right_iff] at h2len
            linarith
          -- Both Icc intervals have same a and b, so they're equal
          simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at h1a h2a h1b h2b ⊢
          simp [h1a, h2a, h1b, h2b]
        · -- Non-degenerate case: derive parity contradiction
          -- From h_side_eq: bisect.fst of B₁ = bisect.snd of B₂
          -- So (B₁.side i).a = (B₂.side i).midpoint = (B₂.side i).a + |B₂.side i|ₗ/2
          have h_fst_a := BoundedInterval.bisect_fst_a (B₁.side i)
          have h_snd_a := BoundedInterval.bisect_snd_a (B₂.side i)
          have hB2_nonempty : B₂.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₂ hB₂
          have h_side2_nonempty := Box.side_nonempty_of_nonempty B₂ hB2_nonempty i
          have h_order2 := BoundedInterval.nonempty_implies_le _ h_side2_nonempty
          have h_mid := BoundedInterval.midpoint_eq_a_add_half_length (B₂.side i) h_order2
          -- From h_side_eq, left endpoints are equal
          have h_a_eq : (B₁.side i).bisect.fst.a = (B₂.side i).bisect.snd.a := congrArg (·.a) h_side_eq
          rw [h_fst_a, h_snd_a, h_mid] at h_a_eq
          -- Now we have: B₁.side i.a = B₂.side i.a + |B₂.side i|ₗ/2
          -- Substitute grid formulas
          rw [hj₁, hj₂, h_len₂] at h_a_eq
          -- j₁ * step = j₂ * step + step/2 where step = |B.side i|ₗ / 2^(k'+2)
          have hstep_pos : (0:ℝ) < |B.side i|ₗ / 2 ^ (k' + 2) := by
            apply div_pos
            · exact lt_of_le_of_ne (BoundedInterval.length_nonneg _) (Ne.symm hL)
            · positivity
          -- This gives j₁ = j₂ + 1/2, impossible for natural numbers
          -- Cancel (B.side i).a from both sides
          have h_cancel : j₁ * (|B.side i|ₗ / 2^(k'+1)) =
                          j₂ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) / 2 := by
            have := h_a_eq; linarith
          -- Multiply both sides by 2^(k'+2) / L to get: 2*j₁ = 2*j₂ + 1
          have h2k1_ne : (2:ℝ) ^ (k' + 1) ≠ 0 := by positivity
          have hL_pos : (0:ℝ) < |B.side i|ₗ := lt_of_le_of_ne (BoundedInterval.length_nonneg _) (Ne.symm hL)
          have hL_ne : |B.side i|ₗ ≠ 0 := hL
          have h_step_ne : |B.side i|ₗ / 2^(k'+1) ≠ 0 := by positivity
          have h_parity : (2 * j₁ : ℝ) = 2 * j₂ + 1 := by
            -- From h_cancel: j₁ * step = j₂ * step + step/2
            -- Multiply both sides by 2, then cancel step
            have h2 : 2 * (j₁ * (|B.side i|ₗ / 2^(k'+1))) =
                      2 * j₂ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) := by linarith
            have h3 : (|B.side i|ₗ / 2^(k'+1)) * (2 * j₁) = (|B.side i|ₗ / 2^(k'+1)) * (2 * j₂ + 1) := by
              ring_nf at h2 ⊢; linarith
            exact mul_left_cancel₀ h_step_ne h3
          -- 2*j₁ is even, 2*j₂+1 is odd: contradiction via omega
          have h_eq_nat : 2 * j₁ = 2 * j₂ + 1 := by
            have := h_parity
            norm_cast at this
          omega
      · -- snd = fst cross case: symmetric to fst = snd
        by_cases hL : |B.side i|ₗ = 0
        · -- Degenerate case: identical to fst = snd case
          have h1a : (B₁.side i).a = (B.side i).a := by rw [hj₁, hL]; simp
          have h2a : (B₂.side i).a = (B.side i).a := by rw [hj₂, hL]; simp
          have h1len : |B₁.side i|ₗ = 0 := by rw [h_len₁, hL]; simp
          have h2len : |B₂.side i|ₗ = 0 := by rw [h_len₂, hL]; simp
          have hB1_nonempty : B₁.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₁ hB₁
          have hB2_nonempty : B₂.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₂ hB₂
          have h1b : (B₁.side i).b = (B₁.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₁ hB1_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            unfold BoundedInterval.length at h1len
            simp only [max_eq_right_iff] at h1len
            linarith
          have h2b : (B₂.side i).b = (B₂.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₂ hB2_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            unfold BoundedInterval.length at h2len
            simp only [max_eq_right_iff] at h2len
            linarith
          simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at h1a h2a h1b h2b ⊢
          simp [h1a, h2a, h1b, h2b]
        · -- Non-degenerate case: derive parity contradiction (symmetric argument)
          -- From h_side_eq: bisect.snd of B₁ = bisect.fst of B₂
          -- So (B₁.side i).midpoint = (B₂.side i).a
          have h_snd_a := BoundedInterval.bisect_snd_a (B₁.side i)
          have h_fst_a := BoundedInterval.bisect_fst_a (B₂.side i)
          have hB1_nonempty : B₁.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₁ hB₁
          have h_side1_nonempty := Box.side_nonempty_of_nonempty B₁ hB1_nonempty i
          have h_order1 := BoundedInterval.nonempty_implies_le _ h_side1_nonempty
          have h_mid := BoundedInterval.midpoint_eq_a_add_half_length (B₁.side i) h_order1
          -- From h_side_eq, left endpoints are equal
          have h_a_eq : (B₁.side i).bisect.snd.a = (B₂.side i).bisect.fst.a := congrArg (·.a) h_side_eq
          rw [h_snd_a, h_fst_a, h_mid] at h_a_eq
          -- Now we have: B₁.side i.a + |B₁.side i|ₗ/2 = B₂.side i.a
          -- Substitute grid formulas
          rw [hj₁, hj₂, h_len₁] at h_a_eq
          -- This gives j₁ + 1/2 = j₂, impossible for natural numbers
          -- Cancel (B.side i).a from both sides
          have h_cancel : j₁ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) / 2 =
                          j₂ * (|B.side i|ₗ / 2^(k'+1)) := by
            have := h_a_eq; linarith
          -- Multiply both sides by 2^(k'+2) / L to get: 2*j₁ + 1 = 2*j₂
          have h2k1_ne : (2:ℝ) ^ (k' + 1) ≠ 0 := by positivity
          have hL_pos : (0:ℝ) < |B.side i|ₗ := lt_of_le_of_ne (BoundedInterval.length_nonneg _) (Ne.symm hL)
          have hL_ne : |B.side i|ₗ ≠ 0 := hL
          have h_step_ne : |B.side i|ₗ / 2^(k'+1) ≠ 0 := by positivity
          have h_parity : (2 * j₁ + 1 : ℝ) = 2 * j₂ := by
            -- From h_cancel: j₁ * step + step/2 = j₂ * step
            -- Multiply both sides by 2, then cancel step
            have h2 : 2 * j₁ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) =
                      2 * j₂ * (|B.side i|ₗ / 2^(k'+1)) := by linarith
            have h3 : (|B.side i|ₗ / 2^(k'+1)) * (2 * j₁ + 1) = (|B.side i|ₗ / 2^(k'+1)) * (2 * j₂) := by
              ring_nf at h2 ⊢; linarith
            exact mul_left_cancel₀ h_step_ne h3
          -- 2*j₁+1 is odd, 2*j₂ is even: contradiction via omega
          have h_eq_nat : 2 * j₁ + 1 = 2 * j₂ := by
            have := h_parity
            norm_cast at this
          omega
      · -- snd = snd case: endpoint equality implies parent equality
        obtain ⟨ha, hb⟩ := BoundedInterval.bisect_snd_eq_endpoints h_side_eq
        -- Both sides are Icc with same endpoints
        simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at ha hb ⊢
        simp [ha, hb]

/-- Diameter bound after k iterations of subdivision.
    Each iteration reduces diameter by factor of √2. -/
lemma diameter_subdivide_iter {d:ℕ} (B: Box d) (hB: B.toSet.Nonempty) (k: ℕ) :
    ∀ B' ∈ subdivide_iter B k, B'.diameter ≤ B.diameter / (Real.sqrt 2) ^ k := by
  induction k with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton, pow_zero, div_one]
    intro B' hB'; rw [hB']
  | succ k ih =>
    intro B' hB'
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB''_mem, hB'_sub⟩ := hB'
    -- B'' is in subdivide_iter B k, and B' is in B''.subdivide
    have hB''_diam := ih B'' hB''_mem
    -- Need: B'' is nonempty to apply subdivide_diameter_bound
    have hB''_nonempty : B''.toSet.Nonempty := subdivide_iter_nonempty B hB k B'' hB''_mem
    have hB'_diam := subdivide_diameter_bound B'' hB''_nonempty B' hB'_sub
    calc B'.diameter
        ≤ B''.diameter / Real.sqrt 2 := hB'_diam
      _ ≤ (B.diameter / (Real.sqrt 2) ^ k) / Real.sqrt 2 := by
          apply div_le_div_of_nonneg_right hB''_diam (Real.sqrt_nonneg 2)
      _ = B.diameter / ((Real.sqrt 2) ^ k * Real.sqrt 2) := by rw [div_div]
      _ = B.diameter / (Real.sqrt 2 * (Real.sqrt 2) ^ k) := by ring_nf
      _ = B.diameter / (Real.sqrt 2) ^ (k + 1) := by rw [pow_succ']

end Box
