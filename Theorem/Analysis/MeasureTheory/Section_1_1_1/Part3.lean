import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Def.Analysis.MeasureTheory.Section_1_1_1.Part2
open BoundedInterval


/- If x < sSup X and X is not empty, then there exists z ∈ X with x < z -/
/- We don't need to assume that X is BddAbove
-(if X is not BddAbove, we get that sSup X = 0 (the junk value) and the result still follows -/
theorem lt_sSup_of_ne_sSup {X : Set ℝ} {x b : ℝ} (_hBddAbove : BddAbove X) (_hb : b = sSup X)
    (hb_notin : b ∉ X) (hx : x ∈ X) (hx_le_b : x ≤ b) : x < b := by
  by_contra! h;  exact hb_notin (hx_le_b.antisymm h ▸ hx)

/-- Show a < x when a = sInf X and a ∉ X -/
theorem sInf_lt_of_ne_sInf {X : Set ℝ} {a x : ℝ} (_hBddBelow : BddBelow X) (_ha : a = sInf X)
    (ha_notin : a ∉ X) (hx : x ∈ X) (ha_le_x : a ≤ x) : a < x := by
  by_contra! h; exact ha_notin (h.antisymm ha_le_x ▸ hx)

/-- Use order-connectedness to show x ∈ X when x ∈ \[w, z\] and w, z ∈ X -/
theorem mem_of_mem_Icc_ordConnected {X : Set ℝ}
    (hOrdConn : ∀ ⦃x : ℝ⦄, x ∈ X → ∀ ⦃y : ℝ⦄, y ∈ X → Set.Icc x y ⊆ X)
    {x w z : ℝ} (hw : w ∈ X) (hz : z ∈ X) (hx : x ∈ Set.Icc w z) : x ∈ X :=
  hOrdConn hw hz hx

/-- A set of reals is bounded and order-connected if and only if it equals some bounded interval. -/
theorem BoundedInterval.ordConnected_iff (X:Set ℝ) :
    Bornology.IsBounded X ∧ X.OrdConnected ↔ ∃ I: BoundedInterval, X = I := by
  constructor
  · -- Non-trivial direction: if X is bounded and order-connected,
    -- then X = I for some BoundedInterval I
    -- Strategy:
    -- 1. Handle the empty case: If X = ∅, use Ioo 0 0 (the empty interval representation)
    -- 2. For non-empty X:
    --    a. Use boundedness to show X has infimum and supremum (bounded sets in ℝ are bounded above and below)
    --    b. Extract endpoints: a = sInf X, b = sSup X
    --    c. Determine interval type based on endpoint membership:
    --       - If a ∈ X ∧ b ∈ X → use Icc a b
    --       - If a ∈ X ∧ b ∉ X → use Ico a b
    --       - If a ∉ X ∧ b ∈ X → use Ioc a b
    --       - If a ∉ X ∧ b ∉ X → use Ioo a b
    --    d. Show X equals the constructed interval:
    --       - X ⊆ interval: Use that a = sInf X and b = sSup X
    --       - interval ⊆ X: Use order-connectedness (if x, y ∈ X, then [x, y] ⊆ X)
    intro ⟨hBounded, hOrdConn⟩
    by_cases hEmpty : X = ∅
    · -- Step 1: Empty case
      use Ioo 0 0
      simp [set_Ioo]
      exact hEmpty
    · -- Step 2: Non-empty case
      have hNonempty : X.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
      rw [Set.ordConnected_def] at hOrdConn
      -- Step 2a: Get boundedness above and below
      -- Use that bounded sets in ℝ are contained in some Icc, which gives bounds directly
      rw [Chapter9.isBounded_def] at hBounded
      obtain ⟨M, hM_pos, hX_subset⟩ := hBounded
      have hBddBelow : BddBelow X := ⟨-M, fun x hx => (hX_subset hx).1⟩
      have hBddAbove : BddAbove X := ⟨M, fun x hx => (hX_subset hx).2⟩
      -- Step 2b: Extract endpoints
      set a := sInf X
      set b := sSup X
      -- Step 2c: Determine interval type based on endpoint membership
      by_cases ha : a ∈ X
      · by_cases hb : b ∈ X
        · -- Case: a ∈ X ∧ b ∈ X → use Icc a b
          use Icc a b; simp [set_Icc]; ext x; constructor
          · intro hx; simp [Set.mem_Icc]
            exact ⟨csInf_le hBddBelow hx, le_csSup hBddAbove hx⟩
          · intro hx; simp [Set.mem_Icc] at hx; exact (hOrdConn ha hb) hx
        · -- Case: a ∈ X ∧ b ∉ X → use Ico a b
          use Ico a b; simp [set_Ico]; ext x; constructor
          · intro hx; simp [Set.mem_Ico]
            exact ⟨csInf_le hBddBelow hx, lt_sSup_of_ne_sSup hBddAbove rfl hb hx (le_csSup hBddAbove hx)⟩
          · intro hx; simp [Set.mem_Ico] at hx
            have hb_eq : b = sSup X := rfl
            obtain ⟨z, hz, hxz⟩ := exists_lt_of_lt_csSup hNonempty
              (by rw [←hb_eq]; exact hx.2)
            exact mem_of_mem_Icc_ordConnected hOrdConn ha hz ⟨hx.1, le_of_lt hxz⟩
      · by_cases hb : b ∈ X
        · -- Case: a ∉ X ∧ b ∈ X → use Ioc a b
          use Ioc a b; simp [set_Ioc]; ext x; constructor
          · intro hx; simp [Set.mem_Ioc]
            exact ⟨sInf_lt_of_ne_sInf hBddBelow rfl ha hx (csInf_le hBddBelow hx), le_csSup hBddAbove hx⟩
          · intro hx; simp [Set.mem_Ioc] at hx
            by_cases hx_eq_b : x = b
            · rw [hx_eq_b]; exact hb
            · have ha_eq : a = sInf X := rfl
              obtain ⟨w, hw, hwx⟩ := exists_lt_of_csInf_lt  hNonempty
                (by rw [←ha_eq]; exact hx.1)
              exact mem_of_mem_Icc_ordConnected hOrdConn hw hb ⟨le_of_lt hwx, hx.2⟩
        · -- Case: a ∉ X ∧ b ∉ X → use Ioo a b
          use Ioo a b; simp [set_Ioo]; ext x; constructor
          · intro hx; simp [Set.mem_Ioo]
            exact ⟨sInf_lt_of_ne_sInf hBddBelow rfl ha hx (csInf_le hBddBelow hx),
              lt_sSup_of_ne_sSup hBddAbove rfl hb hx (le_csSup hBddAbove hx)⟩
          · intro hx; simp [Set.mem_Ioo] at hx
            have ha_eq : a = sInf X := rfl; have hb_eq : b = sSup X := rfl
            obtain ⟨z, hz, hxz⟩ := exists_lt_of_lt_csSup hNonempty
              (by rw [←hb_eq]; exact hx.2)
            obtain ⟨w, hw, hwx⟩ := exists_lt_of_csInf_lt hNonempty
              (by rw [←ha_eq]; exact hx.1)
            exact mem_of_mem_Icc_ordConnected hOrdConn hw hz ⟨le_of_lt hwx, le_of_lt hxz⟩
  · -- Trivial direction: if X = I for some BoundedInterval I, then X is bounded and order-connected
    intro ⟨I, hX⟩
    have hX' : X = (I : Set ℝ) := hX
    constructor
    · -- Show X is bounded
      rw [hX']
      exact Bornology.IsBounded.of_boundedInterval I
    · -- Show X is order-connected: by case analysis on the four interval types,
      -- using `Set.ordConnected_def` and proving that for any `x, y` in the interval
      -- and `z` in `[x, y]`, we have `z` in the interval
      rw [hX']
      rw [Set.ordConnected_def]
      intro x hx y hy z hz
      cases I with
      | Ioo a b =>
        simp [set_Ioo, Set.mem_Ioo] at hx hy hz; simp [Set.mem_Ioo]
        exact ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
      | Icc a b =>
        simp [set_Icc, Set.mem_Icc] at hx hy hz; simp [Set.mem_Icc]
        exact ⟨le_trans hx.1 hz.1, le_trans hz.2 hy.2⟩
      | Ioc a b =>
        simp [set_Ioc, Set.mem_Ioc] at hx hy hz; simp [Set.mem_Ioc]
        exact ⟨lt_of_lt_of_le hx.1 hz.1, le_trans hz.2 hy.2⟩
      | Ico a b =>
        simp [set_Ico, Set.mem_Ico] at hx hy hz; simp [Set.mem_Ico]
        exact ⟨le_trans hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩

/-- The intersection of two bounded intervals is again a bounded interval. -/
theorem BoundedInterval.inter (I J: BoundedInterval) : ∃ K : BoundedInterval, (I:Set ℝ) ∩ (J:Set ℝ) = (K:Set ℝ) := by
  -- Strategy: Use the characterization theorem `BoundedInterval.ordConnected_iff`
  -- Step 1: Show that (I:Set ℝ) ∩ (J:Set ℝ) is bounded
  -- Step 2: Show that (I:Set ℝ) ∩ (J:Set ℝ) is order-connected
  -- Step 3: Apply the characterization theorem
  have hBounded : Bornology.IsBounded ((I:Set ℝ) ∩ (J:Set ℝ)) := by
    -- The intersection is a subset of I, which is bounded
    exact (Bornology.IsBounded.of_boundedInterval I).subset Set.inter_subset_left
  have hOrdConn : ((I:Set ℝ) ∩ (J:Set ℝ)).OrdConnected := by
    -- Both I and J are order-connected (from ordConnected_iff)
    have hI_ordConn : (I:Set ℝ).OrdConnected := by
      exact (BoundedInterval.ordConnected_iff (I:Set ℝ)).mpr ⟨I, rfl⟩ |>.2
    have hJ_ordConn : (J:Set ℝ).OrdConnected := by
      exact (BoundedInterval.ordConnected_iff (J:Set ℝ)).mpr ⟨J, rfl⟩ |>.2
    -- Intersection of order-connected sets is order-connected
    exact Set.OrdConnected.inter hI_ordConn hJ_ordConn
  exact (BoundedInterval.ordConnected_iff ((I:Set ℝ) ∩ (J:Set ℝ))).mp ⟨hBounded, hOrdConn⟩

