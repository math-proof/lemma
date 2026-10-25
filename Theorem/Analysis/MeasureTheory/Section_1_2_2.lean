import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15


/-!
# Introduction to Measure Theory, Section 1.2.2: Lebesgue measurability

A companion to (the introduction to) Section 1.2.2 of the book "An introduction to Measure Theory".

-/

/-- Lemma 1.2.13(i) (Every open set is Lebesgue measurable). -/
theorem IsOpen.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsOpen E) : LebesgueMeasurable E := by
  -- Strategy: For any ε > 0, choose U = E itself
  -- Since E is already open, U \ E = E \ E = ∅, and m*(∅) = 0 ≤ ε
  intro ε hε
  -- Witness: U = E
  use E
  constructor
  · -- E is open (given)
    exact hE
  constructor
  · -- E ⊆ E (reflexivity)
    rfl
  · -- Show m*(E \ E) ≤ ε
    have h_empty : E \ E = ∅ := Set.diff_self
    rw [h_empty]
    have h_zero : Lebesgue_outer_measure (∅ : Set (EuclideanSpace' d)) = 0 :=
      Lebesgue_outer_measure.of_empty d
    rw [h_zero]
    exact le_of_lt hε

/-- Helper: For a finset of pairwise almost disjoint dyadic boxes, the outer measure of their
    union equals the sum of their volumes. -/
private lemma Lebesgue_outer_measure.sum_of_almost_disjoint_finset {d : ℕ} (_hd_pos : 0 < d)
    {t : Finset ℕ} {Q : ℕ → Box d} (_hQ_dyadic : ∀ i, (Q i).IsDyadic)
    (hQ : Pairwise (Function.onFun AlmostDisjoint Q)) :
    Lebesgue_outer_measure (⋃ i ∈ t, (Q i).toSet) = ∑ i ∈ t, ((Q i).volume : EReal) := by
  -- Direct proof using elementary set theory (avoids flawed union_of_separated approach)
  -- Convert to Fin (t.card) indexed boxes via Finset.equivFin
  let equiv := t.equivFin
  let B' : Fin t.card → Box d := fun i => Q (equiv.symm i).val
  -- Show the biUnion equals the iUnion over Fin t.card
  have h_eq : (⋃ i ∈ t, (Q i).toSet) = ⋃ (i : Fin t.card), (B' i).toSet := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_iUnion, B']
    constructor
    · intro ⟨i, hi, hx⟩
      exact ⟨equiv ⟨i, hi⟩, by simp [hx]⟩
    · intro ⟨i, hx⟩
      exact ⟨(equiv.symm i).val, (equiv.symm i).property, hx⟩
  rw [h_eq]
  -- The finite union is elementary
  have hElem : IsElementary (⋃ (i : Fin t.card), (B' i).toSet) :=
    IsElementary.iUnion_boxes B'
  -- Almost-disjointness for Fin-indexed boxes
  have hB'_disj : Pairwise (Function.onFun AlmostDisjoint B') := by
    intro i j h_ne
    simp only [Function.onFun, B']
    apply hQ
    intro h_eq
    have heq : equiv.symm i = equiv.symm j := Subtype.ext h_eq
    exact h_ne (equiv.symm.injective heq)
  -- Apply IsElementary.almost_disjoint: measure = ∑ volumes
  have h_measure := IsElementary.almost_disjoint hElem B' rfl hB'_disj
  -- Convert measure to outer measure
  have h_outer := Lebesgue_outer_measure.elementary _ hElem
  -- Sum conversion: ∑ i : Fin t.card, (B' i).volume = ∑ i ∈ t, (Q i).volume
  have h_sum_eq : ∑ i : Fin t.card, (B' i).volume = ∑ i ∈ t, (Q i).volume := by
    conv_rhs => rw [← Finset.sum_attach]
    refine Finset.sum_equiv equiv.symm ?_ ?_
    · intro i; simp [Finset.mem_univ, Finset.mem_attach]
    · intro i _; simp only [B']
  rw [h_outer, h_measure, h_sum_eq]
  -- Now need: ↑(∑ i ∈ t, (Q i).volume) = ∑ i ∈ t, ↑(Q i).volume
  exact EReal.coe_finset_sum (fun i _ => Box.volume_nonneg _)

/-- Helper: Bounded closed sets are measurable (Lemma 1.2.13(ii) for bounded case).
    For bounded closed E (compact by Heine-Borel), show that for any ε > 0,
    there exists open U ⊇ E with m\*(U \ E) ≤ ε. -/
private lemma IsClosed.measurable_of_bounded {d:ℕ} {E: Set (EuclideanSpace' d)}
    (hE: IsClosed E) (hE_bounded : Bornology.IsBounded E) : LebesgueMeasurable E := by
  intro ε hε
  -- Empty case
  by_cases hE_empty : E = ∅
  · use ∅
    refine ⟨isOpen_empty, ?_, ?_⟩
    · rw [hE_empty]
    · simp [Lebesgue_outer_measure.of_empty]; exact le_of_lt hε
  -- Non-empty bounded closed E is compact
  have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
  -- Get open U with m*(U) ≤ m*(E) + ε/2
  have hε_half_pos : (0 : EReal) < ε / 2 := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top =>
      show (0 : EReal) < ⊤ / 2
      -- ⊤ / 2 = ⊤ in EReal since 2 > 0 and 2 ≠ ⊤
      have : (⊤ : EReal) / 2 = ⊤ := by
        have h2_pos : (0 : EReal) < 2 := by norm_num
        have h2_ne_top : (2 : EReal) ≠ ⊤ := by
          intro h
          have : (2 : EReal) = (2 : ℝ) := rfl
          rw [this] at h
          exact EReal.coe_ne_top 2 h
        exact EReal.top_div_of_pos_ne_top h2_pos h2_ne_top
      rw [this]
      exact EReal.zero_lt_top
    | coe r =>
      have hr_pos : 0 < r := EReal.coe_pos.mp hε
      rw [show (2 : EReal) = (2 : ℝ) from rfl, ← EReal.coe_div r 2]
      exact EReal.coe_pos.mpr (half_pos hr_pos)
  obtain ⟨U, hU_open, hE_sub_U, hU_meas⟩ := Lebesgue_outer_measure.exists_open_superset_measure_le E (ε/2) hε_half_pos
  use U
  refine ⟨hU_open, hE_sub_U, ?_⟩
  -- Key: show m*(U \ E) ≤ ε
  -- U \ E is open
  have h_diff_open : IsOpen (U \ E) := hU_open.sdiff hE
  -- Handle d = 0 separately
  by_cases hd : d = 0
  · -- In dimension 0, EuclideanSpace' 0 = Fin 0 → ℝ is a subsingleton
    -- Since E is nonempty and E ⊆ U, and U is nonempty (contains E), we have E = U
    -- Therefore U \ E = ∅, so m*(U \ E) = 0 ≤ ε
    subst hd
    have : Subsingleton (EuclideanSpace' 0) := by
      unfold EuclideanSpace'
      infer_instance
    have hU_nonempty : U.Nonempty := hE_nonempty.mono hE_sub_U
    have hEU_eq : E = U := by
      apply Set.Subset.antisymm hE_sub_U
      intro x hx
      obtain ⟨y, hy⟩ := hE_nonempty
      have hxy : x = y := Subsingleton.elim x y
      rw [hxy]
      exact hy
    rw [hEU_eq, Set.diff_self, Lebesgue_outer_measure.of_empty]
    exact le_of_lt hε
  push_neg at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  -- If U \ E is empty, trivial
  by_cases h_diff_empty : U \ E = ∅
  · rw [h_diff_empty, Lebesgue_outer_measure.of_empty]; exact le_of_lt hε
  -- Main argument: U \ E is nonempty open, decompose into cubes
  have h_diff_nonempty : (U \ E).Nonempty := Set.nonempty_iff_ne_empty.mpr h_diff_empty
  obtain ⟨Q, hQ_union, hQ_dyadic, hQ_pairwise⟩ := h_diff_open.eq_union_boxes hd_pos (U \ E) h_diff_nonempty
  rw [hQ_union]
  -- m*(⋃ Q_n) = ∑ |Q_n|
  have h_measure_eq : Lebesgue_outer_measure (⋃ n, (Q n).toSet) = ∑' n, (Q n).volume.toEReal := by
    have h1 := Lebesgue_outer_measure.union_of_almost_disjoint hQ_pairwise
    simp_rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _),
             IsElementary.measure_of_box] at h1
    exact h1
  rw [h_measure_eq]
  -- Use compactness: E is compact (closed + bounded)
  -- EuclideanSpace ℝ (Fin d) is finite-dimensional, hence ProperSpace
  -- By Heine-Borel: closed + bounded = compact in proper spaces
  have hE_compact : IsCompact E := Metric.isCompact_of_isClosed_isBounded hE hE_bounded
  calc ∑' n, (Q n).volume.toEReal
      = Lebesgue_outer_measure (⋃ n, (Q n).toSet) := h_measure_eq.symm
    _ = Lebesgue_outer_measure (U \ E) := by rw [← hQ_union]
    _ ≤ ε / 2 := by
        -- Key: E is compact, so m*(E) is finite (not ⊥ or ⊤)
        have hE_finite : Lebesgue_outer_measure E ≠ ⊤ :=
          Lebesgue_outer_measure.finite_of_compact hE_compact
        have hE_ne_bot : Lebesgue_outer_measure E ≠ ⊥ := by
          have h_nonneg : 0 ≤ Lebesgue_outer_measure E := Lebesgue_outer_measure.nonneg E
          intro h_eq
          rw [h_eq] at h_nonneg
          -- 0 ≤ ⊥ is false in EReal
          exact not_le.mpr EReal.bot_lt_zero h_nonneg

        -- For each finite N, show ∑_{i < N} vol(Q_i) ≤ ε/2
        have h_finite_sum_bound : ∀ (t : Finset ℕ),
            ∑ i ∈ t, ((Q i).volume : EReal) ≤ ε / 2 := by
          intro t
          -- Handle empty finset case
          by_cases ht_empty : t = ∅
          · rw [ht_empty]
            simp
            exact le_of_lt hε_half_pos
          -- Now t is nonempty
          -- Let F_t = ⋃_{i ∈ t} Q_i
          let F_t := ⋃ i ∈ t, (Q i).toSet
          -- F_t is compact (finite union of compact boxes)
          have hF_compact : IsCompact F_t := by
            -- Each box is compact (product of compact intervals)
            have hQ_compact : ∀ i ∈ t, IsCompact ((Q i).toSet) := by
              intro i _
              exact Box.isCompact (Q i) (Box.IsDyadic.all_sides_Icc (hQ_dyadic i))
            -- Finite union of compact sets is compact
            exact Finset.isCompact_biUnion t hQ_compact
          -- E ∩ F_t = ∅ (since F_t ⊆ U\E)
          have hE_F_disj : E ∩ F_t = ∅ := by
            ext x
            simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, F_t]
            intro hxE
            simp only [Set.mem_iUnion, not_exists]
            intro i hi
            -- x ∈ E and x ∈ Q_i, but Q_i ⊆ U\E
            have hQ_sub : (Q i).toSet ⊆ U \ E := by
              have : (Q i).toSet ⊆ ⋃ n, (Q n).toSet := by
                intro y hy
                exact Set.mem_iUnion_of_mem i hy
              rw [← hQ_union] at this
              exact this
            intro hxi
            exact (hQ_sub hxi).2 hxE
          -- By compactness: set_dist E F_t > 0 (t is nonempty, so F_t is nonempty)
          have ht_ne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht_empty
          obtain ⟨i, hi⟩ := ht_ne
          have hF_nonempty : F_t.Nonempty :=
            (Box.toSet_nonempty_of_IsDyadic (hQ_dyadic i)).mono (Set.subset_biUnion_of_mem hi)
          have h_sep : set_dist E F_t > 0 :=
            dist_of_disj_compact_pos E F_t hE_nonempty hF_nonempty hE_compact hF_compact hE_F_disj
          -- By separation: m*(E ∪ F_t) = m*(E) + m*(F_t)
          have h_add : Lebesgue_outer_measure (E ∪ F_t) =
                       Lebesgue_outer_measure E + Lebesgue_outer_measure F_t :=
            Lebesgue_outer_measure.union_of_separated hd_pos h_sep
          -- E ∪ F_t ⊆ U
          have h_sub : E ∪ F_t ⊆ U := by
            intro x hx
            cases hx with
            | inl hxE => exact hE_sub_U hxE
            | inr hxF =>
              -- F_t ⊆ ⋃ n, Q_n = U\E ⊆ U
              have : F_t ⊆ ⋃ n, (Q n).toSet := by
                intro y hy
                simp [F_t] at hy
                obtain ⟨i, hi, hyi⟩ := hy
                exact Set.mem_iUnion_of_mem i hyi
              have hF_sub : (⋃ n, (Q n).toSet) ⊆ U := by
                rw [← hQ_union]
                exact Set.diff_subset
              exact hF_sub (this hxF)
          -- So m*(E ∪ F_t) ≤ m*(U) ≤ m*(E) + ε/2
          have h_bound : Lebesgue_outer_measure (E ∪ F_t) ≤ Lebesgue_outer_measure E + ε / 2 := by
            calc Lebesgue_outer_measure (E ∪ F_t)
                ≤ Lebesgue_outer_measure U := Lebesgue_outer_measure.mono h_sub
              _ ≤ Lebesgue_outer_measure E + ε / 2 := hU_meas
          -- Therefore m*(E) + m*(F_t) ≤ m*(E) + ε/2, so m*(F_t) ≤ ε/2
          rw [h_add] at h_bound
          -- Cancellation: m*(E) + m*(F_t) ≤ m*(E) + ε/2 implies m*(F_t) ≤ ε/2
          have h_F_bound : Lebesgue_outer_measure F_t ≤ ε / 2 := by
            -- Use EReal.sub_le_of_le_add': if a ≤ b + c then a - b ≤ c
            have h1 : Lebesgue_outer_measure E + Lebesgue_outer_measure F_t - Lebesgue_outer_measure E ≤ ε / 2 :=
              EReal.sub_le_of_le_add' h_bound
            -- Since m*(E) is finite (not ⊥ or ⊤), we have (m*(E) + m*(F_t)) - m*(E) = m*(F_t)
            -- Case analysis on m*(E) being a real number
            have h_cancel : Lebesgue_outer_measure E + Lebesgue_outer_measure F_t - Lebesgue_outer_measure E = Lebesgue_outer_measure F_t := by
              cases h : Lebesgue_outer_measure E with
              | bot => exact absurd h hE_ne_bot
              | top => exact absurd h hE_finite
              | coe r =>
                -- m*(E) = r (a real number), so the goal is already r + m*(F_t) - r = m*(F_t)
                exact EReal.add_sub_cancel_left
            rw [h_cancel] at h1
            exact h1
          -- Finally: m*(F_t) = ∑_{i ∈ t} vol(Q_i) by almost disjoint union
          calc ∑ i ∈ t, ((Q i).volume : EReal)
              = Lebesgue_outer_measure F_t := by
                symm
                exact Lebesgue_outer_measure.sum_of_almost_disjoint_finset hd_pos hQ_dyadic hQ_pairwise
            _ ≤ ε / 2 := h_F_bound

        -- Now: ∑' n, vol(Q_n) ≤ ε/2 by supremum of finite sums
        have hvol_nonneg : ∀ n, 0 ≤ (Q n).volume := fun n => Box.volume_nonneg _
        have h_range_bound : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((Q i).volume : EReal) ≤ ε / 2 :=
          fun N => h_finite_sum_bound (Finset.range N)
        have h_tsum_bound : ∑' n, ((Q n).volume : EReal) ≤ ε / 2 :=
          EReal.tsum_le_of_sum_range_le hvol_nonneg h_range_bound
        -- Convert back using h_measure_eq
        calc Lebesgue_outer_measure (U \ E)
            = Lebesgue_outer_measure (⋃ n, (Q n).toSet) := by rw [hQ_union]
          _ = ∑' n, ((Q n).volume : EReal) := h_measure_eq
          _ ≤ ε / 2 := h_tsum_bound
    _ ≤ ε := by
        cases ε with
        | bot => exact absurd hε (not_lt.mpr bot_le)
        | top => exact le_top
        | coe r =>
          have hr_pos : 0 < r := EReal.coe_pos.mp hε
          rw [show (2 : EReal) = (2 : ℝ) from rfl, ← EReal.coe_div r 2]
          exact EReal.coe_le_coe_iff.mpr (half_le_self (le_of_lt hr_pos))

/-- Lemma 1.2.13(ii) (Every closed set is Lebesgue measurable). -/
theorem IsClosed.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsClosed E) : LebesgueMeasurable E := by
  -- Write E = ⋃_{n=0}^∞ (E ∩ closedBall 0 n)
  have h_union : E = ⋃ n : ℕ, E ∩ Metric.closedBall 0 n := (Metric.iUnion_inter_closedBall_nat E 0).symm
  rw [h_union]
  -- Each E ∩ closedBall 0 n is closed (intersection of closed sets) and bounded
  have h_closed : ∀ n : ℕ, IsClosed (E ∩ Metric.closedBall 0 n) :=
    fun n => hE.inter Metric.isClosed_closedBall
  have h_bounded : ∀ n : ℕ, Bornology.IsBounded (E ∩ Metric.closedBall 0 n) :=
    fun n => Metric.isBounded_closedBall.subset Set.inter_subset_right
  -- Apply IsClosed.measurable_of_bounded to each piece
  have h_meas : ∀ n : ℕ, LebesgueMeasurable (E ∩ Metric.closedBall 0 n) :=
    fun n => IsClosed.measurable_of_bounded (h_closed n) (h_bounded n)
  -- Inline countable union proof (Lemma 1.2.13(vi) is defined later in this file)
  intro ε hε
  -- Convert EReal ε to a real number ε' with 0 < ε' ≤ ε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r =>
      have hr : 0 < r := EReal.coe_pos.mp hε
      exact ⟨r, hr, le_refl _⟩
  -- For each n, get U_n open with (E ∩ closedBall 0 n) ⊆ U_n and m*(U_n \ (E ∩ closedBall 0 n)) ≤ ε'/2^(n+1)
  have hδ_pos : ∀ n, (0:EReal) < ε' / 2^(n+1) := fun n => by
    apply EReal.div_pos (EReal.coe_pos.mpr hε'_pos)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_pos.mpr (by positivity)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_ne_top ((2:ℝ)^(n+1))
  choose U hU_open hE_sub hU_diff using fun n => h_meas n (ε' / 2^(n+1)) (hδ_pos n)
  -- The open set is ⋃ n, U n
  use ⋃ n, U n
  constructor
  · exact isOpen_iUnion hU_open
  constructor
  · apply Set.iUnion_mono; intro n; exact hE_sub n
  · -- m*((⋃ n, U n) \ (⋃ n, E ∩ closedBall 0 n)) ≤ ε
    have h_diff_subset : (⋃ (n : ℕ), U n) \ (⋃ (n : ℕ), E ∩ Metric.closedBall 0 ↑n) ⊆ ⋃ (n : ℕ), (U n \ (E ∩ Metric.closedBall 0 ↑n)) := by
      intro x ⟨hx_in_U, hx_not_in_E⟩
      simp only [Set.mem_iUnion] at hx_in_U hx_not_in_E ⊢
      obtain ⟨k, hxk⟩ := hx_in_U
      use k
      constructor
      · exact hxk
      · intro hx_Ek; exact hx_not_in_E ⟨k, hx_Ek⟩
    calc Lebesgue_outer_measure ((⋃ (n : ℕ), U n) \ (⋃ (n : ℕ), E ∩ Metric.closedBall 0 ↑n))
        ≤ Lebesgue_outer_measure (⋃ (n : ℕ), (U n \ (E ∩ Metric.closedBall 0 ↑n))) :=
          Lebesgue_outer_measure.mono h_diff_subset
      _ ≤ ∑' (n : ℕ), Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n)) :=
          Lebesgue_outer_measure.union_le _
      _ ≤ ∑' (n : ℕ), ((ε' / 2^(n+1) : ℝ) : EReal) := by
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_f_nonneg : ∀ n, 0 ≤ Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n)) :=
            fun n => Lebesgue_outer_measure.nonneg _
          have h_le_coe : ∀ n, Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n)) ≤ ((ε' / 2^(n+1) : ℝ) : EReal) := by
            intro n
            calc Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n))
                ≤ (↑ε' : EReal) / 2^(n+1) := hU_diff n
              _ = ↑(ε' / 2^(n+1)) := by
                  rw [EReal.coe_div]
                  congr 1
                  exact Eq.symm (EReal.coe_pow 2 (n + 1))
          exact EReal.tsum_le_coe_tsum_of_forall_le h_f_nonneg h_nonneg h_summable h_le_coe
      _ = ε' := by
          have h_sum : ∑' n : ℕ, (ε' : ℝ) / 2^(n+1) = ε' := tsum_geometric_eps ε' hε'_pos
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          rw [← EReal.coe_tsum_of_nonneg h_nonneg h_summable, h_sum]
      _ ≤ ε := hε'_le

