import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Def.Analysis.MeasureTheory.Section_1_2_1.Part2
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


namespace Box

/-- Diameter is always nonnegative -/
lemma diameter_nonneg {d:ℕ} (B: Box d) : 0 ≤ B.diameter := by
  unfold diameter
  by_cases h : B.toSet.Nonempty
  · obtain ⟨x, hx⟩ := h
    apply le_csSup
    · -- The set is bounded above
      use (∑ i : Fin d, |B.side i|ₗ)
      intro r ⟨y, hy, z, hz, hr⟩
      -- dist y z is bounded by sum of side lengths
      rw [hr]
      -- y, z ∈ B.toSet means ∀ i, y i ∈ B.side i and z i ∈ B.side i
      have hy_coord : ∀ i, y i ∈ (B.side i).toSet := by
        intro i; exact hy i
      have hz_coord : ∀ i, z i ∈ (B.side i).toSet := by
        intro i; exact hz i
      -- For each coordinate, the difference is bounded by the side length
      have coord_bound : ∀ i, |(y - z) i| ≤ |B.side i|ₗ := by
        intro i
        have hy_i := hy_coord i
        have hz_i := hz_coord i
        -- All interval types have the same bound: |y i - z i| ≤ max (b - a) 0
        -- This is because both y i and z i are in [a,b] (or (a,b) with open endpoints)
        cases h_side : B.side i with
        | Ioo a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
        | Icc a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
        | Ioc a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
        | Ico a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
      -- Now prove that √(∑ (y i - z i)²) ≤ ∑ |B.side i|ₗ
      -- We use: √(∑ xᵢ²) ≤ ∑ √(xᵢ²) = ∑ |xᵢ| (subadditivity of sqrt)
      have sqrt_sum_le : (∑ i, (y i - z i) ^ 2).sqrt ≤ ∑ i, |(y i - z i)| := by
        -- ℓ² ≤ ℓ¹ norm: √(∑ xᵢ²) ≤ ∑ |xᵢ|
        calc (∑ i, (y i - z i) ^ 2).sqrt
            = (∑ i, |(y i - z i)| ^ 2).sqrt := by
                congr 1; congr 1; ext i; rw [sq_abs]
          _ ≤ ∑ i, (|(y i - z i)| ^ 2).sqrt := by
                -- Apply sqrt subadditivity lemma
                apply Real.sqrt_sum_le_sum_sqrt
                intro i; exact sq_nonneg _
          _ = ∑ i, |(y i - z i)| := by
                congr 1; ext i
                rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]
      calc √(∑ i, (y i - z i) ^ 2)
          ≤ ∑ i, |(y i - z i)| := sqrt_sum_le
        _ = ∑ i, |(y - z) i| := by rfl
        _ ≤ ∑ i, |B.side i|ₗ := by
            apply Finset.sum_le_sum
            intro i _
            exact coord_bound i
    · -- 0 is in the set (distance from any point to itself)
      use x, hx, x, hx
      simp
  · -- Empty box has diameter 0
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h]
    simp [sSup]

/-- Empty box has diameter 0 -/
lemma diameter_of_empty {d:ℕ} (B: Box d) (h: B.toSet = ∅) :
    B.diameter = 0 := by
  unfold diameter
  simp [h, sSup]

/-- Any two points in a box have Euclidean distance at most the diameter -/
lemma dist_le_diameter {d:ℕ} (B: Box d) {x y: EuclideanSpace' d}
    (hx: x ∈ B.toSet) (hy: y ∈ B.toSet) :
    √(∑ i, (x i - y i)^2) ≤ B.diameter := by
  unfold diameter
  apply le_csSup
  · -- The set is bounded above
    use (∑ i : Fin d, |B.side i|ₗ)
    intro r ⟨z, hz, w, hw, hr⟩
    -- dist z w is bounded by sum of side lengths
    rw [hr]
    -- z, w ∈ B.toSet means ∀ i, z i ∈ B.side i and w i ∈ B.side i
    have hz_coord : ∀ i, z i ∈ (B.side i).toSet := by
      intro i; exact hz i
    have hw_coord : ∀ i, w i ∈ (B.side i).toSet := by
      intro i; exact hw i
    -- For each coordinate, the difference is bounded by the side length
    have coord_bound : ∀ i, |(z - w) i| ≤ |B.side i|ₗ := by
      intro i
      have hz_i := hz_coord i
      have hw_i := hw_coord i
      -- All interval types have the same bound: |z i - w i| ≤ max (b - a) 0
      cases h_side : B.side i with
      | Ioo a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
      | Icc a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
      | Ioc a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
      | Ico a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
    -- Now prove that √(∑ (z i - w i)²) ≤ ∑ |B.side i|ₗ
    have sqrt_sum_le : (∑ i, (z i - w i) ^ 2).sqrt ≤ ∑ i, |(z i - w i)| := by
      -- ℓ² ≤ ℓ¹ norm: √(∑ xᵢ²) ≤ ∑ |xᵢ|
      calc (∑ i, (z i - w i) ^ 2).sqrt
          = (∑ i, |(z i - w i)| ^ 2).sqrt := by
              congr 1; congr 1; ext i; rw [sq_abs]
        _ ≤ ∑ i, (|(z i - w i)| ^ 2).sqrt := by
              apply Real.sqrt_sum_le_sum_sqrt
              intro i; exact sq_nonneg _
        _ = ∑ i, |(z i - w i)| := by
              congr 1; ext i
              rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]
    calc √(∑ i, (z i - w i) ^ 2)
        ≤ ∑ i, |(z i - w i)| := sqrt_sum_le
      _ = ∑ i, |(z - w) i| := by rfl
      _ ≤ ∑ i, |B.side i|ₗ := by
          apply Finset.sum_le_sum
          intro i _
          exact coord_bound i
  · -- √(∑ (x i - y i)²) is in the set
    exact ⟨x, hx, y, hy, rfl⟩

/-- For any nonempty interval and target value less than the length,
    we can find two points in the interval with separation exceeding the target.
    This is the key density fact: achievable differences are dense in \[0, length\]. -/
lemma BoundedInterval.exists_points_with_diff {I : BoundedInterval}
    (h_nonempty : I.toSet.Nonempty) {t : ℝ} (ht_nonneg : 0 ≤ t) (ht : t < |I|ₗ) :
    ∃ x ∈ I.toSet, ∃ y ∈ I.toSet, t < |x - y| := by
  -- Since t < |I|ₗ = max (b - a) 0 and t ≥ 0, we have b - a > t ≥ 0
  have h_len_pos : 0 < |I|ₗ := lt_of_le_of_lt ht_nonneg ht
  cases I with
  | Icc a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Closed: use endpoints a and b
    refine ⟨a, Set.left_mem_Icc.mpr (le_of_lt h_ab), b, Set.right_mem_Icc.mpr (le_of_lt h_ab), ?_⟩
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < b - a)]
    linarith
  | Ioo a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Open: use points close to endpoints
    set δ := ((b - a) - t) / 2 with hδ_def
    have h_δ_pos : 0 < δ := by linarith
    have hx_mem : a + δ / 2 ∈ Set.Ioo a b := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    have hy_mem : b - δ / 2 ∈ Set.Ioo a b := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    refine ⟨a + δ / 2, hx_mem, b - δ / 2, hy_mem, ?_⟩
    have h_diff : (b - δ / 2) - (a + δ / 2) = (b - a) - δ := by ring
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < (b - δ / 2) - (a + δ / 2)), h_diff]
    linarith
  | Ioc a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Left open, right closed: use point close to a and b
    set δ := ((b - a) - t) / 2 with hδ_def
    have h_δ_pos : 0 < δ := by linarith
    have hx_mem : a + δ / 2 ∈ Set.Ioc a b := Set.mem_Ioc.mpr ⟨by linarith, by linarith⟩
    have hy_mem : b ∈ Set.Ioc a b := Set.mem_Ioc.mpr ⟨h_ab, le_refl b⟩
    refine ⟨a + δ / 2, hx_mem, b, hy_mem, ?_⟩
    have h_diff : b - (a + δ / 2) = (b - a) - δ / 2 := by ring
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < b - (a + δ / 2)), h_diff]
    linarith
  | Ico a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Left closed, right open: use a and point close to b
    set δ := ((b - a) - t) / 2 with hδ_def
    have h_δ_pos : 0 < δ := by linarith
    have hx_mem : a ∈ Set.Ico a b := Set.mem_Ico.mpr ⟨le_refl a, h_ab⟩
    have hy_mem : b - δ / 2 ∈ Set.Ico a b := Set.mem_Ico.mpr ⟨by linarith, by linarith⟩
    refine ⟨a, hx_mem, b - δ / 2, hy_mem, ?_⟩
    have h_diff : (b - δ / 2) - a = (b - a) - δ / 2 := by ring
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < (b - δ / 2) - a), h_diff]
    linarith

/-- The diameter of a nonempty box equals the diagonal length √(∑ |side i|ₗ²).
    This is the key fact: the supremum of pairwise distances equals the diagonal.
    For closed intervals, the diagonal is achieved at corners.
    For open intervals, the diagonal is the limit (supremum) of achievable distances. -/
lemma diameter_eq_sqrt_sum_sq {d:ℕ} (B: Box d) (h: B.toSet.Nonempty) :
    B.diameter = √(∑ i, |B.side i|ₗ^2) := by
  unfold diameter
  -- Use csSup_eq_of_forall_le_of_forall_lt_exists_gt:
  -- if s.Nonempty ∧ (∀ a ∈ s, a ≤ b) ∧ (∀ c < b, ∃ a ∈ s, c < a), then sSup s = b
  let s := { r | ∃ x ∈ B.toSet, ∃ y ∈ B.toSet, r = √(∑ i, (x i - y i)^2) }
  let b := √(∑ i, |B.side i|ₗ^2)
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · -- s is nonempty
    obtain ⟨x, hx⟩ := h
    exact ⟨√(∑ i, (x i - x i)^2), x, hx, x, hx, rfl⟩
  · -- ∀ a ∈ s, a ≤ b (upper bound)
    intro r ⟨x, hx, y, hy, hr⟩
    rw [hr]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    -- |x i - y i|² ≤ |B.side i|ₗ²
    have hx_i : x i ∈ (B.side i).toSet := hx i
    have hy_i : y i ∈ (B.side i).toSet := hy i
    have coord_bound : |x i - y i| ≤ |B.side i|ₗ := by
      cases h_side : B.side i <;>
          simp [BoundedInterval.toSet, h_side] at hx_i hy_i <;>
          simp [BoundedInterval.length] <;>
          (left; rw [abs_sub_le_iff]; constructor <;> linarith [hx_i.1, hx_i.2, hy_i.1, hy_i.2])
    calc (x i - y i)^2 = |x i - y i|^2 := by rw [sq_abs]
      _ ≤ |B.side i|ₗ^2 := by
          apply sq_le_sq' <;> [linarith [abs_nonneg (x i - y i), coord_bound]; exact coord_bound]
  · -- ∀ c < b, ∃ a ∈ s, c < a (density: can get arbitrarily close to b)
    intro c hc
    -- Need to find x, y ∈ B with √(∑ (x i - y i)²) > c
    -- Strategy: for each coordinate, pick points near opposite ends of the interval
    -- The resulting distance will be close to √(∑ side²)
    -- Since c < √(∑ side²), we can find ε > 0 such that c < √(∑ side²) - ε
    -- Then pick x, y such that |x i - y i| ≥ |side i| - δ for small enough δ
    -- This gives √(∑ (x i - y i)²) ≥ √(∑ (side - δ)²) > c for small δ
    --
    -- For the formal proof, we use that intervals are nonempty (from h_nonempty)
    -- and that we can pick points with controlled distances from endpoints.
    by_cases h_zero : (∑ i, |B.side i|ₗ^2) = 0
    · -- All sides have length 0, so b = 0
      -- c < 0 is impossible since distances are ≥ 0
      simp only [h_zero, Real.sqrt_zero] at hc
      -- c < 0, but any distance is ≥ 0, so we need c < some distance ≥ 0
      -- Since c < 0, we have c < 0 ≤ any distance
      obtain ⟨x, hx⟩ := h
      use 0
      constructor
      · exact ⟨x, hx, x, hx, by simp⟩
      · linarith
    · -- Some side has positive length
      -- Use the characterization: √(∑ side²) > c means ∑ side² > c²
      have h_pos : 0 < ∑ i, |B.side i|ₗ^2 := by
        apply lt_of_le_of_ne
        · apply Finset.sum_nonneg; intro i _; exact sq_nonneg _
        · exact Ne.symm h_zero
      -- Get ε such that c + ε < √(∑ side²)
      have h_c_lt : c < √(∑ i, |B.side i|ₗ^2) := hc
      -- Since c < √(∑ side²), we have c² < ∑ side² (for c ≥ 0) or c < 0
      by_cases hc_nonneg : 0 ≤ c
      · -- c ≥ 0 case: we need to construct points with large distance
        -- Strategy: use exists_points_with_diff for positive-length coordinates
        -- Each interval is nonempty (from h: B.toSet.Nonempty)
        have h_interval_nonempty : ∀ i, (B.side i).toSet.Nonempty := by
          intro i; obtain ⟨x, hx⟩ := h
          exact ⟨x i, hx i⟩
        -- We'll construct points coordinate-wise with ≥ for all and > for positive-length
        let ratio := c / √(∑ i, |B.side i|ₗ^2)
        have h_ratio_lt_one : ratio < 1 := by
          show c / √(∑ i, |B.side i|ₗ^2) < 1
          rw [div_lt_one (Real.sqrt_pos.mpr h_pos)]
          exact h_c_lt
        have h_ratio_nonneg : 0 ≤ ratio := by
          show 0 ≤ c / √(∑ i, |B.side i|ₗ^2)
          exact div_nonneg hc_nonneg (Real.sqrt_nonneg _)
        -- For positive-length coordinates: get strict inequality
        have h_exists_points : ∀ i, ∃ xi ∈ (B.side i).toSet, ∃ yi ∈ (B.side i).toSet,
            |B.side i|ₗ * ratio ≤ |xi - yi| ∧
            (0 < |B.side i|ₗ → |B.side i|ₗ * ratio < |xi - yi|) := by
          intro i
          by_cases h_len_zero : |B.side i|ₗ = 0
          · -- Zero-length interval: xi = yi gives 0 ≤ 0
            obtain ⟨xi, hxi⟩ := h_interval_nonempty i
            refine ⟨xi, hxi, xi, hxi, ?_, ?_⟩
            · simp [h_len_zero]
            · simp [h_len_zero]
          · -- Positive-length interval: use exists_points_with_diff
            have h_len_pos : 0 < |B.side i|ₗ := by
              apply lt_of_le_of_ne; simp [BoundedInterval.length]; exact Ne.symm h_len_zero
            have h_target_lt : |B.side i|ₗ * ratio < |B.side i|ₗ := by
              calc |B.side i|ₗ * ratio < |B.side i|ₗ * 1 := by
                    apply mul_lt_mul_of_pos_left h_ratio_lt_one h_len_pos
                _ = |B.side i|ₗ := mul_one _
            obtain ⟨xi, hxi, yi, hyi, hlt⟩ := BoundedInterval.exists_points_with_diff
              (h_interval_nonempty i) (mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg)
              h_target_lt
            exact ⟨xi, hxi, yi, hyi, le_of_lt hlt, fun _ => hlt⟩
        -- Use Classical.choose to extract the points
        classical
        let x' : Fin d → ℝ := fun i => (h_exists_points i).choose
        let y' : Fin d → ℝ := fun i => (h_exists_points i).choose_spec.2.choose
        have hx_mem : ∀ i, x' i ∈ (B.side i).toSet := fun i => (h_exists_points i).choose_spec.1
        have hy_mem : ∀ i, y' i ∈ (B.side i).toSet := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.1
        have h_diff_le : ∀ i, |B.side i|ₗ * ratio ≤ |x' i - y' i| := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.2.1
        have h_diff_lt : ∀ i, 0 < |B.side i|ₗ → |B.side i|ₗ * ratio < |x' i - y' i| := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.2.2
        -- x, y ∈ B.toSet
        let x : EuclideanSpace' d := .toLp 2 x'
        let y : EuclideanSpace' d := .toLp 2 y'
        have hx_box : x ∈ B.toSet := fun i => hx_mem i
        have hy_box : y ∈ B.toSet := fun i => hy_mem i
        -- The distance √(∑ (x_i - y_i)²) > c
        use √(∑ i, (x i - y i)^2)
        constructor
        · exact ⟨x, hx_box, y, hy_box, rfl⟩
        · -- Need: c < √(∑ (x_i - y_i)²)
          rw [← Real.sqrt_sq hc_nonneg]
          apply Real.sqrt_lt_sqrt (sq_nonneg c)
          -- Need: c² < ∑ (x_i - y_i)²
          -- c² = ∑ (side * ratio)² and we have ≤ for all, < for at least one positive side
          have h_target : c^2 = ∑ i, (|B.side i|ₗ * ratio)^2 := by
            have h_sum_nonneg : 0 ≤ ∑ i : Fin d, |B.side i|ₗ^2 :=
              Finset.sum_nonneg (fun i _ => sq_nonneg (|B.side i|ₗ))
            have h_sqrt_ne : √(∑ i, |B.side i|ₗ^2) ≠ 0 := Real.sqrt_ne_zero'.mpr h_pos
            calc c^2 = (√(∑ i, |B.side i|ₗ^2) * ratio)^2 := by
                  show c^2 = (√(∑ i, |B.side i|ₗ^2) * (c / √(∑ i, |B.side i|ₗ^2)))^2
                  field_simp
              _ = (∑ i, |B.side i|ₗ^2) * ratio^2 := by
                  rw [mul_pow, Real.sq_sqrt h_sum_nonneg]
              _ = ∑ i, |B.side i|ₗ^2 * ratio^2 := Finset.sum_mul _ _ _
              _ = ∑ i, (|B.side i|ₗ * ratio)^2 := by congr 1; ext i; ring
          rw [h_target]
          -- Since ∑ side² > 0, at least one side is positive
          have h_exists_pos : ∃ j, 0 < |B.side j|ₗ := by
            by_contra h_all_zero; push_neg at h_all_zero
            have h_sum_zero : (∑ i, |B.side i|ₗ^2) = 0 := by
              apply Finset.sum_eq_zero; intro i _
              have : |B.side i|ₗ ≤ 0 := h_all_zero i
              have h_nonneg : 0 ≤ |B.side i|ₗ := by simp [BoundedInterval.length]
              have : |B.side i|ₗ = 0 := le_antisymm this h_nonneg
              simp [this]
            exact h_zero h_sum_zero
          obtain ⟨j, hj_pos⟩ := h_exists_pos
          apply Finset.sum_lt_sum
          · intro i _
            have h_sq : (|B.side i|ₗ * ratio)^2 ≤ |x i - y i|^2 := by
              apply sq_le_sq' _ (h_diff_le i)
              calc -(|x i - y i|) ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
                _ ≤ |B.side i|ₗ * ratio := mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg
            calc (|B.side i|ₗ * ratio)^2 ≤ |x i - y i|^2 := h_sq
              _ = (x i - y i)^2 := by rw [sq_abs]
          · use j, Finset.mem_univ j
            have h_sq_lt : (|B.side j|ₗ * ratio)^2 < |x j - y j|^2 := by
              -- From h_diff_lt we know side * ratio < |x j - y j|, so |x j - y j| > 0
              have h_diff_pos : 0 < |x j - y j| :=
                lt_of_le_of_lt (mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg)
                  (h_diff_lt j hj_pos)
              apply sq_lt_sq' _ (h_diff_lt j hj_pos)
              calc -(|x j - y j|) < 0 := neg_neg_of_pos h_diff_pos
                _ ≤ |B.side j|ₗ * ratio := mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg
            calc (|B.side j|ₗ * ratio)^2 < |x j - y j|^2 := h_sq_lt
              _ = (x j - y j)^2 := by rw [sq_abs]
      · -- c < 0 case: any distance ≥ 0 > c
        push_neg at hc_nonneg
        obtain ⟨x, hx⟩ := h
        use 0
        constructor
        · exact ⟨x, hx, x, hx, by simp⟩
        · linarith

/-- If a box intersects two sets, any two points (one from each set)
    in the box have distance at most the diameter -/
lemma diameter_ge_dist_of_intersects {d:ℕ} (B: Box d) (E F : Set (EuclideanSpace' d))
    (hE : (B.toSet ∩ E).Nonempty) (hF : (B.toSet ∩ F).Nonempty) :
    set_dist E F ≤ B.diameter := by
  obtain ⟨x, hx_box, hx_E⟩ := hE
  obtain ⟨y, hy_box, hy_F⟩ := hF
  -- set_dist E F ≤ dist x y (by definition of set_dist as infimum)
  have h_dist : set_dist E F ≤ dist x y := by
    unfold set_dist
    apply csInf_le
    · -- Bounded below by 0
      use 0
      intro r ⟨p, hp, hr⟩
      rw [← hr]
      exact dist_nonneg
    · -- The distance from x to y is in the set
      simp only [Set.mem_image]
      use (x, y)
      exact ⟨Set.mem_prod.mpr ⟨hx_E, hy_F⟩, rfl⟩
  -- dist x y ≤ B.diameter (by dist_le_diameter)
  have h_le_diam : √(∑ i, (x i - y i)^2) ≤ B.diameter :=
    dist_le_diameter B hx_box hy_box
  -- Note: For EuclideanSpace' d, dist x y = √(∑ i, (x i - y i)^2)
  have h_eq : dist x y = √(∑ i, (x i - y i)^2) := by
    simp only [EuclideanSpace.dist_eq]
    congr 1
    congr 1
    ext i
    rw [Real.dist_eq, sq_abs]
  -- Combine
  calc set_dist E F
      ≤ dist x y := h_dist
    _ = √(∑ i, (x i - y i)^2) := h_eq
    _ ≤ B.diameter := h_le_diam

/-- If B.diameter < set\_dist E F, then B cannot intersect both E and F.
    This is the core geometric fact needed for finite additivity of separated sets. -/
lemma not_intersects_both_of_diameter_lt {d:ℕ} (B: Box d) (E F : Set (EuclideanSpace' d))
    (h : B.diameter < set_dist E F) :
    ¬((B.toSet ∩ E).Nonempty ∧ (B.toSet ∩ F).Nonempty) := by
  intro ⟨hE, hF⟩
  -- If B intersects both, then set_dist E F ≤ B.diameter
  have := diameter_ge_dist_of_intersects B E F hE hF
  -- But we assumed B.diameter < set_dist E F
  linarith

end Box
