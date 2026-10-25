import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
import Abbrev.Analysis.MeasureTheory.Section_1_2_2


/-- Lemma 1.2.13(iii) (Every null set is Lebesgue measurable). -/
theorem IsNull.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsNull E) : LebesgueMeasurable E := by
  -- Strategy: For any ε > 0, since m*(E) = 0, get a box cover with total volume < ε,
  -- then inflate boxes to open sets. The union is open and contains E.
  intro ε hε
  -- Handle dimension 0 separately
  by_cases hd : d = 0
  · -- In dimension 0, EuclideanSpace' 0 is a single point.
    -- Since m*(E) = 0 and m*(univ) = 1 for nonempty sets in d=0, E must be empty.
    -- Use U = E = ∅, which is open, E ⊆ U, and U \ E = ∅ has measure 0.
    subst hd
    -- In d=0: m*(E) = if E.Nonempty then 1 else 0
    -- hE : IsNull E is an abbrev for Lebesgue_outer_measure E = 0
    have hE' : Lebesgue_outer_measure E = 0 := hE
    rw [Lebesgue_outer_measure_of_dim_zero] at hE'
    simp only [ite_eq_right_iff, one_ne_zero] at hE'
    -- hE' : E.Nonempty → False, i.e., E = ∅
    have hE_empty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE'
    use ∅
    refine ⟨isOpen_empty, ?_, ?_⟩
    · rw [hE_empty]
    · simp only [Set.empty_diff]
      rw [Lebesgue_outer_measure.of_empty]
      exact le_of_lt hε
  -- Now d > 0
  push_neg at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  -- m*(E) = 0 implies m*(E) ≠ ⊤
  have h_finite : Lebesgue_outer_measure E ≠ ⊤ := by rw [hE]; exact EReal.zero_ne_top
  -- Convert EReal ε to a real number
  -- Since ε > 0, get a real ε' with 0 < ε' and ε' ≤ ε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r =>
      have hr : 0 < r := EReal.coe_pos.mp hε
      exact ⟨r, hr, le_refl _⟩
  -- Get an ε'/2-close box cover
  have hε2_pos : 0 < ε' / 2 := by linarith
  obtain ⟨S, hS_cover, hS_vol⟩ := Lebesgue_outer_measure.exists_cover_close hd_pos E (ε' / 2) hε2_pos h_finite
  -- hS_vol : ∑' n, (S n).volume.toEReal ≤ m*(E) + ε'/2 = 0 + ε'/2 = ε'/2
  rw [hE] at hS_vol
  simp only [zero_add] at hS_vol
  -- Inflate each box to get an open set containing it
  -- Use δₙ = ε' / 2^(n+2) so that ∑ δₙ = ε'/2
  let δ : ℕ → ℝ := fun n => ε' / 2 / 2 ^ (n + 1)
  have hδ_pos : ∀ n, 0 < δ n := fun n => by simp only [δ]; positivity
  -- Get inflated boxes using Box.inflate
  have h_inflate := fun n => Box.inflate (S n) (δ n) (hδ_pos n)
  choose U' hU'_subset hU'_open hU'_vol using h_inflate
  -- Define U as union of interiors of inflated boxes
  let U := ⋃ n, interior (U' n).toSet
  use U
  constructor
  · -- U is open (union of open sets)
    exact isOpen_iUnion (fun n => isOpen_interior)
  constructor
  · -- E ⊆ U
    calc E ⊆ ⋃ n, (S n).toSet := hS_cover
         _ ⊆ ⋃ n, interior (U' n).toSet := Set.iUnion_mono (fun n => hU'_subset n)
  · -- m*(U \ E) ≤ ε
    -- Key bounds: m*(U \ E) ≤ m*(U) ≤ ∑ |U' n|ᵥ ≤ ∑ (|S n|ᵥ + δ n) ≤ ε'/2 + ε'/2 = ε' ≤ ε
    have h1 : Lebesgue_outer_measure (U \ E) ≤ Lebesgue_outer_measure U :=
      Lebesgue_outer_measure.mono Set.diff_subset
    have h2 : Lebesgue_outer_measure U ≤ ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) := by
      have : U = ⋃ n, interior (U' n).toSet := rfl
      rw [this]
      exact Lebesgue_outer_measure.union_le _
    -- Each interior has measure ≤ box volume
    have h3 : ∀ n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ (U' n).volume.toEReal := by
      intro n
      calc Lebesgue_outer_measure (interior (U' n).toSet)
          ≤ Lebesgue_outer_measure (U' n).toSet := Lebesgue_outer_measure.mono interior_subset
        _ = (IsElementary.box (U' n)).measure.toEReal := by
            rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _)]
        _ = (U' n).volume.toEReal := by rw [IsElementary.measure_of_box]
    -- Each inflated box volume ≤ original + δ
    have h4 : ∀ n, (U' n).volume.toEReal ≤ ((S n).volume + δ n).toEReal := by
      intro n
      exact EReal.coe_le_coe_iff.mpr (hU'_vol n)
    -- The sum splits: ∑ (|S n|ᵥ + δ n) = ∑ |S n|ᵥ + ∑ δ n ≤ ε'/2 + ε'/2 = ε' ≤ ε
    have hδ_sum : ∑' n, (δ n : ℝ) = ε' / 2 := by
      simp only [δ, div_div]
      have h := tsum_geometric_two' (ε' / 2)
      convert h using 1
      congr 1
      ext n
      ring_nf
    -- Combine the bounds to show m*(U \ E) ≤ ε' ≤ ε
    -- Strategy:
    -- m*(U\E) ≤ m*(U) ≤ ∑ m*(interior U'_n) ≤ ∑ vol(U'_n) ≤ ∑ (vol(S_n) + δ_n)
    --         ≤ ∑ vol(S_n) + ∑ δ_n ≤ ε'/2 + ε'/2 = ε' ≤ ε
    -- The key steps use h1, h2, h3, h4, hS_vol, hδ_sum, hε'_le
    have h_sum_le : ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ε' := by
      -- Each interior measure ≤ vol(U' n) ≤ vol(S n) + δ n
      -- Sum: ∑ vol(S n) ≤ ε'/2, ∑ δ n = ε'/2, so total ≤ ε'
      -- First show δ is summable (geometric series)
      have hδ_summable : Summable δ := by
        simp only [δ, div_div]
        exact (summable_geometric_two' (ε' / 2)).congr (fun n => by ring_nf)
      -- Show volumes are summable (from the bound hS_vol)
      have hvol_nonneg : ∀ n, 0 ≤ (S n).volume := fun n => Box.volume_nonneg _
      have hvol_sum : Summable (fun n => (S n).volume) := by
        -- Key: use that the partial sums in EReal are bounded
        have h_partial_bound : ∀ t : Finset ℕ, (∑ n ∈ t, (S n).volume : EReal) ≤ ε' / 2 := by
          intro t
          calc (∑ n ∈ t, (S n).volume : EReal)
              ≤ ∑' n, ((S n).volume : EReal) := EReal.finset_sum_le_tsum hvol_nonneg t
            _ ≤ ε' / 2 := hS_vol
        -- In ℝ: partial sums bounded implies summable for nonneg sequences
        have h_partial_real : ∀ t : Finset ℕ, ∑ n ∈ t, (S n).volume ≤ ε' / 2 := by
          intro t
          have h := h_partial_bound t
          have h_coe : (∑ n ∈ t, (S n).volume : EReal) = ↑(∑ n ∈ t, (S n).volume) :=
            (EReal.coe_finset_sum (fun n _ => hvol_nonneg n)).symm
          rw [h_coe] at h; exact EReal.coe_le_coe_iff.mp h
        exact summable_of_sum_le hvol_nonneg h_partial_real
      have hsum_combined : Summable (fun n => (S n).volume + δ n) := hvol_sum.add hδ_summable
      -- Use transitivity through ε' bound:
      -- ∑ m*(interior U'_n) ≤ ∑ vol(U'_n) ≤ ∑ (vol S_n + δ_n) = ∑ vol S_n + ∑ δ_n ≤ ε'/2 + ε'/2 = ε'
      have h_interior_bound : ∀ n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ((S n).volume + δ n : EReal) := by
        intro n
        calc Lebesgue_outer_measure (interior (U' n).toSet)
            ≤ (U' n).volume.toEReal := h3 n
          _ ≤ ((S n).volume + δ n).toEReal := h4 n
          _ = ((S n).volume + δ n : EReal) := rfl
      -- Sum bound: use EReal.tsum_le_coe_tsum_of_forall_le
      have hg_nonneg : ∀ n, 0 ≤ (S n).volume + δ n := fun n => by linarith [hvol_nonneg n, hδ_pos n]
      have h_tsum_bound : ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ∑' n, ((S n).volume + δ n : EReal) :=
        EReal.tsum_le_coe_tsum_of_forall_le (fun n => Lebesgue_outer_measure.nonneg _)
          hg_nonneg hsum_combined h_interior_bound
      -- Key equality: tsums in EReal with coercion can be rewritten
      have h_tsum_eq : ∑' n, (↑(S n).volume + ↑(δ n) : EReal) = ↑(∑' n, ((S n).volume + δ n)) := by
        have h1 : ∑' n, (↑(S n).volume + ↑(δ n) : EReal) = ∑' n, ↑((S n).volume + δ n) := by
          apply tsum_congr
          intro n; exact (EReal.coe_add _ _).symm
        have h2 : ∑' n, (↑((S n).volume + δ n) : EReal) = ↑(∑' n, ((S n).volume + δ n)) :=
          (EReal.coe_tsum_of_nonneg hg_nonneg hsum_combined).symm
        rw [h1, h2]
      calc ∑' n, Lebesgue_outer_measure (interior (U' n).toSet)
          ≤ ∑' n, (↑(S n).volume + ↑(δ n) : EReal) := h_tsum_bound
        _ = ↑(∑' n, ((S n).volume + δ n)) := h_tsum_eq
        _ = ↑(∑' n, (S n).volume + ∑' n, δ n) := by rw [hvol_sum.tsum_add hδ_summable]
        _ = ↑(∑' n, (S n).volume) + ↑(∑' n, δ n) := by rw [EReal.coe_add]
        _ ≤ ↑(ε' / 2) + ↑(ε' / 2) := by
            apply add_le_add
            · have := EReal.coe_tsum_of_nonneg hvol_nonneg hvol_sum
              rw [this]; exact hS_vol
            · rw [hδ_sum]
        _ = ε' := by rw [← EReal.coe_add]; norm_cast; ring
    calc Lebesgue_outer_measure (U \ E)
        ≤ Lebesgue_outer_measure U := h1
      _ ≤ ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) := h2
      _ ≤ ε' := h_sum_le
      _ ≤ ε := hε'_le

/-- A subset of a null set is null. -/
lemma IsNull.subset {d:ℕ} {E F : Set (EuclideanSpace' d)} (hE : IsNull E) (hFE : F ⊆ E) : IsNull F := by
  have := Lebesgue_outer_measure.mono hFE
  rw [hE] at this
  exact le_antisymm this (Lebesgue_outer_measure.nonneg F)

/-- Lemma 1.2.13(iv) (Empty set is measurable). -/
theorem LebesgueMeasurable.empty {d:ℕ} : LebesgueMeasurable (∅: Set (EuclideanSpace' d)) :=

-- use (i) directly

  IsOpen.measurable isOpen_empty

theorem LebesgueMeasurable.empty' {d:ℕ} : LebesgueMeasurable (∅: Set (EuclideanSpace' d)) := by

-- use definition of Lebesgue measurability

  intro ε hε
  use ∅
  constructor
  · exact isOpen_empty
  constructor
  · exact Set.empty_subset ∅
  · have h_empty : ∅ \ ∅ = (∅ : Set (EuclideanSpace' d)) := Set.diff_self
    rw [h_empty]
    rw [Lebesgue_outer_measure.of_empty d]
    exact le_of_lt hε

/-- Lemma 1.2.13(vi) (Countable union of measurable sets is measurable). -/
theorem LebesgueMeasurable.countable_union {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) : LebesgueMeasurable (⋃ n, E n) := by
  -- Use the ε/2^n trick: let ε > 0 be arbitrary
  intro ε hε
  -- Convert EReal ε to a real number ε' with 0 < ε' ≤ ε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r =>
      have hr : 0 < r := EReal.coe_pos.mp hε
      exact ⟨r, hr, le_refl _⟩
  -- For each n, get U_n open with E_n ⊆ U_n and m*(U_n \ E_n) ≤ ε'/2^(n+1)
  have hδ_pos : ∀ n, (0:EReal) < ε' / 2^(n+1) := fun n => by
    apply EReal.div_pos (EReal.coe_pos.mpr hε'_pos)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_pos.mpr (by positivity)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_ne_top ((2:ℝ)^(n+1))
  -- Apply measurability of each E_n with ε'/2^(n+1)
  choose U hU_open hE_sub hU_diff using fun n => hE n (ε' / 2^(n+1)) (hδ_pos n)
  -- The open set is ⋃ n, U n
  use ⋃ n, U n
  constructor
  · -- ⋃ n, U n is open (union of open sets)
    exact isOpen_iUnion hU_open
  constructor
  · -- ⋃ n, E n ⊆ ⋃ n, U n
    apply Set.iUnion_mono
    intro n; exact hE_sub n
  · -- m*((⋃ n, U n) \ (⋃ n, E n)) ≤ ε
    -- Key: (⋃ U_n) \ (⋃ E_n) ⊆ ⋃ (U_n \ E_n)
    have h_diff_subset : (⋃ n, U n) \ (⋃ n, E n) ⊆ ⋃ n, (U n \ E n) := by
      intro x ⟨hx_in_U, hx_not_in_E⟩
      simp only [Set.mem_iUnion] at hx_in_U hx_not_in_E ⊢
      obtain ⟨k, hxk⟩ := hx_in_U
      use k
      constructor
      · exact hxk
      · intro hx_Ek
        exact hx_not_in_E ⟨k, hx_Ek⟩
    calc Lebesgue_outer_measure ((⋃ n, U n) \ (⋃ n, E n))
        ≤ Lebesgue_outer_measure (⋃ n, (U n \ E n)) :=
          Lebesgue_outer_measure.mono h_diff_subset
      _ ≤ ∑' n, Lebesgue_outer_measure (U n \ E n) :=
          Lebesgue_outer_measure.union_le _
      _ ≤ ∑' n, ((ε' / 2^(n+1) : ℝ) : EReal) := by
          -- Use EReal.tsum_le_coe_tsum_of_forall_le
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_f_nonneg : ∀ n, 0 ≤ Lebesgue_outer_measure (U n \ E n) :=
            fun n => Lebesgue_outer_measure.nonneg _
          have h_le_coe : ∀ n, Lebesgue_outer_measure (U n \ E n) ≤ ((ε' / 2^(n+1) : ℝ) : EReal) := by
            intro n
            calc Lebesgue_outer_measure (U n \ E n)
                ≤ (↑ε' : EReal) / 2^(n+1) := hU_diff n
              _ = ↑(ε' / 2^(n+1)) := by
                  rw [EReal.coe_div]
                  congr 1
                  exact Eq.symm (EReal.coe_pow 2 (n + 1))
          exact EReal.tsum_le_coe_tsum_of_forall_le h_f_nonneg h_nonneg h_summable h_le_coe
      _ = ε' := by
          -- ∑ n, ε'/2^(n+1) = ε' (geometric series)
          have h_sum : ∑' n : ℕ, (ε' : ℝ) / 2^(n+1) = ε' := tsum_geometric_eps ε' hε'_pos
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          rw [← EReal.coe_tsum_of_nonneg h_nonneg h_summable, h_sum]
      _ ≤ ε := hε'_le

/-- Lemma 1.2.13(v) (Complement of a measurable set is measurable). -/
theorem LebesgueMeasurable.complement {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) : LebesgueMeasurable (Eᶜ) := by
  -- Strategy: For each n, find open Uₙ ⊇ E with m*(Uₙ \ E) ≤ 1/(n+1).
  -- Let Fₙ = Uₙᶜ (closed). Then Eᶜ ⊇ Fₙ and m*(Eᶜ \ Fₙ) = m*(Uₙ \ E) ≤ 1/(n+1).
  -- Let F = ⋃ Fₙ. Then m*(Eᶜ \ F) = 0 and Eᶜ = F ∪ (Eᶜ \ F).
  -- F is measurable (countable union of closed sets), Eᶜ \ F is null (hence measurable).

  -- Step 1: For each n, get open Uₙ with E ⊆ Uₙ and m*(Uₙ \ E) ≤ 1/(n+1)
  have h_eps_pos : ∀ n : ℕ, (0 : EReal) < 1 / (n + 1 : ℕ) := fun n => by
    have h1 : (0 : EReal) < 1 := EReal.coe_pos.mpr (by norm_num : (0 : ℝ) < 1)
    have h2 : (0 : EReal) < (n + 1 : ℕ) := by
      simp only [Nat.cast_add, Nat.cast_one]
      exact EReal.coe_pos.mpr (by linarith : (0 : ℝ) < n + 1)
    exact EReal.div_pos h1 h2 (EReal.coe_ne_top _)
  choose U hU_open hE_sub_U hU_diff using fun n => hE (1 / (n + 1 : ℕ)) (h_eps_pos n)

  -- Step 2: Define Fₙ = Uₙᶜ (closed sets)
  let F_n : ℕ → Set (EuclideanSpace' d) := fun n => (U n)ᶜ
  have hF_closed : ∀ n, IsClosed (F_n n) := fun n => (hU_open n).isClosed_compl

  -- Key set-theoretic fact: Eᶜ \ Fₙ = Uₙ \ E
  have h_diff_eq : ∀ n, Eᶜ \ F_n n = U n \ E := fun n => by
    simp only [F_n, Set.diff_compl]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]
    tauto

  -- Step 3: Define F = ⋃ Fₙ (F-sigma set)
  let F := ⋃ n, F_n n

  -- Step 4: Show m*(Eᶜ \ F) = 0
  have h_diff_F : ∀ n, Eᶜ \ F ⊆ U n \ E := fun n => by
    have h1 : Eᶜ \ F ⊆ Eᶜ \ F_n n := Set.diff_subset_diff_right (Set.subset_iUnion F_n n)
    rw [h_diff_eq n] at h1
    exact h1

  have h_measure_bound : ∀ n, Lebesgue_outer_measure (Eᶜ \ F) ≤ 1 / (n + 1 : ℕ) := fun n =>
    calc Lebesgue_outer_measure (Eᶜ \ F)
        ≤ Lebesgue_outer_measure (U n \ E) := Lebesgue_outer_measure.mono (h_diff_F n)
      _ ≤ 1 / (n + 1 : ℕ) := hU_diff n

  have h_null : IsNull (Eᶜ \ F) := by
    apply le_antisymm
    · -- Show m*(Eᶜ \ F) ≤ 0 by showing it's ≤ 1/(n+1) for all n
      by_contra h_ne
      push_neg at h_ne
      have h_pos : 0 < Lebesgue_outer_measure (Eᶜ \ F) := h_ne
      -- Get a real ε with 0 < ε ≤ m*(Eᶜ \ F)
      obtain ⟨ε, hε_pos, hε_le⟩ : ∃ ε : ℝ, 0 < ε ∧ (ε : EReal) ≤ Lebesgue_outer_measure (Eᶜ \ F) := by
        cases hm : Lebesgue_outer_measure (Eᶜ \ F) with
        | bot => rw [hm] at h_pos; exact absurd h_pos (not_lt.mpr bot_le)
        | top => exact ⟨1, one_pos, le_top⟩
        | coe r =>
          rw [hm] at h_pos
          have hr : 0 < r := EReal.coe_pos.mp h_pos
          exact ⟨r, hr, le_refl _⟩
      -- Find N with 1/(N+1) < ε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      have hNp1_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hN1 : 1 / ((N : ℝ) + 1) < ε := by
        have h1 : 1 / ε < (N : ℝ) + 1 := lt_of_lt_of_le hN (by norm_cast; exact Nat.le_succ N)
        rw [one_div_lt hNp1_pos hε_pos]; exact h1
      -- h_measure_bound N says m*(Eᶜ \ F) ≤ 1/(N+1)
      have h_bound : Lebesgue_outer_measure (Eᶜ \ F) ≤ 1 / (N + 1 : ℕ) := h_measure_bound N
      have h_eq : (1 : EReal) / (N + 1 : ℕ) = ↑(1 / ((N : ℝ) + 1)) := by
        rw [EReal.coe_div, EReal.coe_one]; norm_cast
      rw [h_eq] at h_bound
      -- ε ≤ m*(Eᶜ \ F) ≤ 1/(N+1) < ε, contradiction
      have h_final : (ε : EReal) < (ε : EReal) := calc
        (ε : EReal) ≤ Lebesgue_outer_measure (Eᶜ \ F) := hε_le
        _ ≤ ↑(1 / ((N : ℝ) + 1)) := h_bound
        _ < ε := EReal.coe_lt_coe_iff.mpr hN1
      exact lt_irrefl (ε : EReal) h_final
    · exact Lebesgue_outer_measure.nonneg _

  -- Step 5: Show Eᶜ = F ∪ (Eᶜ \ F)
  have h_decomp : Eᶜ = F ∪ (Eᶜ \ F) := by
    ext x
    simp only [Set.mem_union, Set.mem_diff]
    constructor
    · intro hx
      by_cases hxF : x ∈ F
      · left; exact hxF
      · right; exact ⟨hx, hxF⟩
    · intro h
      cases h with
      | inl hxF =>
        simp only [F, Set.mem_iUnion] at hxF
        obtain ⟨n, hxFn⟩ := hxF
        simp only [F_n, Set.mem_compl_iff] at hxFn
        have hxE : x ∉ E := fun h => hxFn (hE_sub_U n h)
        exact hxE
      | inr hxEcF => exact hxEcF.1

  -- Step 6: Apply measurability results
  rw [h_decomp]
  have hF_meas : LebesgueMeasurable F := by
    have : F = ⋃ n, F_n n := rfl
    rw [this]
    exact LebesgueMeasurable.countable_union (fun n => (hF_closed n).measurable)
  have hN_meas : LebesgueMeasurable (Eᶜ \ F) := h_null.measurable
  -- Union of two measurable sets
  let S : ℕ → Set (EuclideanSpace' d) := fun n => if n = 0 then F else if n = 1 then Eᶜ \ F else ∅
  have hS_meas : ∀ n, LebesgueMeasurable (S n) := fun n => by
    simp only [S]
    split_ifs with h0 h1
    · exact hF_meas
    · exact hN_meas
    · exact LebesgueMeasurable.empty
  have h_eq : F ∪ (Eᶜ \ F) = ⋃ n, S n := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, S]
    constructor
    · intro h
      cases h with
      | inl hF => exact ⟨0, by simp [hF]⟩
      | inr hN => exact ⟨1, by simp [hN]⟩
    · intro ⟨n, hn⟩
      split_ifs at hn with h0 h1
      · left; exact hn
      · right; exact hn
      · exact absurd hn (Set.notMem_empty x)
  rw [h_eq]
  exact LebesgueMeasurable.countable_union hS_meas

theorem LebesgueMeasurable.finite_union {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hE: ∀ i, LebesgueMeasurable (E i)) : LebesgueMeasurable (⋃ i, E i) := by
  -- Extend E to ℕ-indexed family by padding with empty sets
  let E' : ℕ → Set (EuclideanSpace' d) := fun k => if h : k < n then E ⟨k, h⟩ else ∅
  have hE'_meas : ∀ k, LebesgueMeasurable (E' k) := fun k => by
    simp only [E']
    split_ifs with hk
    · exact hE ⟨k, hk⟩
    · exact LebesgueMeasurable.empty
  -- Show ⋃ i : Fin n, E i = ⋃ k : ℕ, E' k
  have h_eq : (⋃ i : Fin n, E i) = ⋃ k : ℕ, E' k := by
    ext x
    simp only [Set.mem_iUnion, E']
    constructor
    · intro ⟨i, hx⟩
      use i.val
      simp only [i.isLt, ↓reduceDIte, hx]
    · intro ⟨k, hx⟩
      split_ifs at hx with hk
      · exact ⟨⟨k, hk⟩, hx⟩
      · exact absurd hx (Set.notMem_empty x)
  rw [h_eq]
  exact LebesgueMeasurable.countable_union hE'_meas

theorem LebesgueMeasurable.union {d :ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : LebesgueMeasurable (E ∪ F) := by
  -- Express E ∪ F as union over Fin 2
  let S : Fin 2 → Set (EuclideanSpace' d) := ![E, F]
  have hS : ∀ i, LebesgueMeasurable (S i) := fun i => by fin_cases i <;> simp [S, hE, hF]
  have h_eq : E ∪ F = ⋃ i : Fin 2, S i := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, S]
    constructor
    · rintro (hx | hx)
      · exact ⟨0, by simp [hx]⟩
      · exact ⟨1, by simp [hx]⟩
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
  rw [h_eq]
  exact LebesgueMeasurable.finite_union hS

/-- Lemma 1.2.13(vii) (Countable intersection of measurable sets is measurable). -/
theorem LebesgueMeasurable.countable_inter {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) : LebesgueMeasurable (⋂ n, E n) := by
  -- By de Morgan: ⋂ Eₙ = (⋃ Eₙᶜ)ᶜ
  have h_eq : (⋂ n, E n) = (⋃ n, (E n)ᶜ)ᶜ := by
    rw [Set.compl_iUnion]
    simp only [compl_compl]
  rw [h_eq]
  -- Each Eₙᶜ is measurable by (v)
  have hE_compl : ∀ n, LebesgueMeasurable ((E n)ᶜ) := fun n => (hE n).complement
  -- ⋃ Eₙᶜ is measurable by (vi)
  have h_union : LebesgueMeasurable (⋃ n, (E n)ᶜ) := LebesgueMeasurable.countable_union hE_compl
  -- (⋃ Eₙᶜ)ᶜ is measurable by (v) again
  exact h_union.complement

theorem LebesgueMeasurable.finite_inter {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hE: ∀ i, LebesgueMeasurable (E i)) : LebesgueMeasurable (⋂ i, E i) := by
  -- Extend Fin n indexed family to ℕ indexed family with univ for k ≥ n
  let E' : ℕ → Set (EuclideanSpace' d) := fun k => if h : k < n then E ⟨k, h⟩ else Set.univ
  have hE'_meas : ∀ k, LebesgueMeasurable (E' k) := fun k => by
    simp only [E']
    split_ifs with hk
    · exact hE ⟨k, hk⟩
    · -- univ = ∅ᶜ, so measurable by complement of empty
      rw [← Set.compl_empty]
      exact LebesgueMeasurable.empty.complement
  have h_eq : (⋂ i : Fin n, E i) = ⋂ k : ℕ, E' k := by
    ext x
    simp only [Set.mem_iInter, E']
    constructor
    · intro hx k
      split_ifs with hk
      · exact hx ⟨k, hk⟩
      · exact Set.mem_univ x
    · intro hx ⟨i, hi⟩
      have := hx i
      simp only [hi, dite_true] at this
      exact this
  rw [h_eq]
  exact LebesgueMeasurable.countable_inter hE'_meas

theorem LebesgueMeasurable.inter {d :ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : LebesgueMeasurable (E ∩ F) := by
  -- Express E ∩ F as intersection over Fin 2
  let S : Fin 2 → Set (EuclideanSpace' d) := ![E, F]
  have hS : ∀ i, LebesgueMeasurable (S i) := fun i => by fin_cases i <;> simp [S, hE, hF]
  have h_eq : E ∩ F = ⋂ i : Fin 2, S i := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, S]
    constructor
    · intro ⟨hxE, hxF⟩ i
      fin_cases i <;> simp_all
    · intro hx
      exact ⟨hx 0, hx 1⟩
  rw [h_eq]
  exact LebesgueMeasurable.finite_inter hS

/-- Finite intersection indexed by a {name}`Finset` is Lebesgue measurable. -/
lemma LebesgueMeasurable.finset_inter {d : ℕ} {α : Type*} [DecidableEq α]
    {E : α → Set (EuclideanSpace' d)} {S : Finset α}
    (hE : ∀ i ∈ S, LebesgueMeasurable (E i)) :
    LebesgueMeasurable (⋂ i ∈ S, E i) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ]
    rw [← Set.compl_empty]
    exact LebesgueMeasurable.empty.complement
  | insert a S' ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hE
    have hE_a := hE.1
    have hE_rest := fun i hi => hE.2 i hi
    rw [show (⋂ i ∈ insert a S', E i) = E a ∩ (⋂ i ∈ S', E i) by
      ext x
      simp only [Set.mem_iInter, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨h a (Finset.mem_insert_self a S'), fun i hi => h i (Finset.mem_insert_of_mem hi)⟩
      · intro ⟨ha', h⟩ i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact ha'
        · exact h i hi']
    exact LebesgueMeasurable.inter hE_a (ih hE_rest)

/-- Finite union indexed by a {name}`Finset` is Lebesgue measurable. -/
lemma LebesgueMeasurable.finset_union {d : ℕ} {α : Type*} [DecidableEq α]
    {E : α → Set (EuclideanSpace' d)} {S : Finset α}
    (hE : ∀ i ∈ S, LebesgueMeasurable (E i)) :
    LebesgueMeasurable (⋃ i ∈ S, E i) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    exact LebesgueMeasurable.empty
  | insert a S' ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hE
    have hE_a := hE.1
    have hE_rest := fun i hi => hE.2 i hi
    rw [show (⋃ i ∈ insert a S', E i) = E a ∪ (⋃ i ∈ S', E i) by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · intro ⟨i, hi, hx⟩
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · left; exact hx
        · right; exact ⟨i, hi', hx⟩
      · intro h
        cases h with
        | inl h => exact ⟨a, Finset.mem_insert_self a S', h⟩
        | inr h => obtain ⟨i, hi, hx⟩ := h; exact ⟨i, Finset.mem_insert_of_mem hi, hx⟩]
    exact LebesgueMeasurable.union hE_a (ih hE_rest)

/-- If A = B outside a null set N (i.e., A ∩ Nᶜ = B ∩ Nᶜ), then A is measurable if B is. -/
lemma LebesgueMeasurable.of_ae_eq {d : ℕ} {A B N : Set (EuclideanSpace' d)}
    (hB : LebesgueMeasurable B) (hN : IsNull N) (h_eq : A ∩ Nᶜ = B ∩ Nᶜ) :
    LebesgueMeasurable A := by
  -- A = (B ∩ Nᶜ) ∪ (A ∩ N)
  have h_decomp : A = (B ∩ Nᶜ) ∪ (A ∩ N) := by
    ext x
    constructor
    · intro hx
      by_cases hxN : x ∈ N
      · right; exact ⟨hx, hxN⟩
      · left; rw [← h_eq]; exact ⟨hx, hxN⟩
    · intro hx
      cases hx with
      | inl h => rw [← h_eq] at h; exact h.1
      | inr h => exact h.1
  rw [h_decomp]
  apply LebesgueMeasurable.union
  · exact LebesgueMeasurable.inter hB (IsNull.measurable hN).complement
  · exact IsNull.measurable (IsNull.subset hN Set.inter_subset_right)

/-- Closed balls are Lebesgue measurable. -/
lemma LebesgueMeasurable.closedBall {d : ℕ} (c : EuclideanSpace' d) (r : ℝ) :
    LebesgueMeasurable (Metric.closedBall c r) :=
  Metric.isClosed_closedBall.measurable

