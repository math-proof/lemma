import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
import Abbrev.Analysis.MeasureTheory.Section_1_2_2.Part2
  IsOpen.measurable isOpen_empty

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

open BoundedInterval


/-- Lemma 1.2.15(a) (Empty set has zero Lebesgue measure). The proof is missing. -/
@[simp]
theorem Lebesgue_measure.empty {d:ℕ} : Lebesgue_measure (∅: Set (EuclideanSpace' d)) = 0 :=
  -- Direct application of Lebesgue_outer_measure.of_empty since Lebesgue_measure = Lebesgue_outer_measure
  Lebesgue_outer_measure.of_empty d

/-- Helper: Countable additivity for compact sets.
    When all $`E_n` are compact and pairwise disjoint, $`m(⋃ E_n) = ∑' m(E_n)`.
    Key: compact disjoint sets have positive separation, so we can use Lemma 1.2.5. -/
private lemma Lebesgue_measure.countable_union_compact {d:ℕ} (hd : 0 < d)
    {E: ℕ → Set (EuclideanSpace' d)}
    (hcompact: ∀ n, IsCompact (E n))
    (hdisj: Set.univ.PairwiseDisjoint E) :
    Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  -- Direction ≤: Countable subadditivity
  have h_le : Lebesgue_measure (⋃ n, E n) ≤ ∑' n, Lebesgue_measure (E n) :=
    Lebesgue_outer_measure.union_le E
  -- Direction ≥: For each N, m(⋃_{n<N} E_n) = ∑_{n<N} m(E_n) by finite additivity + separation
  have h_ge : ∑' n, Lebesgue_measure (E n) ≤ Lebesgue_measure (⋃ n, E n) := by
    -- For each N, by induction, m(⋃_{n≤N} E_n) = ∑_{n≤N} m(E_n)
    have h_finite_sum : ∀ N : ℕ, Lebesgue_measure (⋃ n ∈ Finset.range N, E n) =
        ∑ n ∈ Finset.range N, Lebesgue_measure (E n) := by
      intro N
      induction N with
      | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        -- ⋃ n ∈ ∅, E n = ∅
        have : (⋃ n ∈ (∅ : Finset ℕ), E n) = ∅ := by simp
        rw [this, Lebesgue_measure.empty]
      | succ N ih =>
        -- ⋃_{n<N+1} E_n = (⋃_{n<N} E_n) ∪ E_N
        have h_union_eq : (⋃ n ∈ Finset.range (N + 1), E n) =
            (⋃ n ∈ Finset.range N, E n) ∪ E N := by
          ext x
          simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union]
          constructor
          · intro ⟨n, ⟨hn, hx⟩⟩
            by_cases hnN : n < N
            · left; exact ⟨n, ⟨hnN, hx⟩⟩
            · right
              have : n = N := Nat.eq_of_lt_succ_of_not_lt hn hnN
              rw [← this]; exact hx
          · intro h
            cases h with
            | inl hl =>
              obtain ⟨n, ⟨hn, hx⟩⟩ := hl
              exact ⟨n, ⟨Nat.lt_succ_of_lt hn, hx⟩⟩
            | inr hr => exact ⟨N, ⟨Nat.lt_succ_self N, hr⟩⟩
        rw [h_union_eq]
        -- The two parts are disjoint
        have h_disj_parts : (⋃ n ∈ Finset.range N, E n) ∩ E N = ∅ := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_range, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro ⟨n, ⟨hn, hxn⟩⟩ hxN
          have hne : n ≠ N := Nat.ne_of_lt hn
          have hdisj_pair : Disjoint (E n) (E N) := hdisj (Set.mem_univ n) (Set.mem_univ N) hne
          exact Set.disjoint_iff.mp hdisj_pair ⟨hxn, hxN⟩
        -- The finite union is compact
        have hcompact_finite : IsCompact (⋃ n ∈ Finset.range N, E n) :=
          Finset.isCompact_biUnion _ (fun n _ => hcompact n)
        -- Use separation of compact disjoint sets
        by_cases h_empty_N : E N = ∅
        · -- If E_N is empty, the union doesn't change
          simp only [h_empty_N, Set.union_empty]
          rw [Finset.sum_range_succ, ih]
          simp [h_empty_N, Lebesgue_measure.empty]
        · by_cases h_empty_union : (⋃ n ∈ Finset.range N, E n) = ∅
          · simp only [h_empty_union, Set.empty_union, Finset.sum_range_succ]
            have h_sum_zero : ∑ n ∈ Finset.range N, Lebesgue_measure (E n) = 0 := by
              have h_all_empty : ∀ n ∈ Finset.range N, E n = ∅ := by
                intro n hn
                by_contra hne
                have hnonempty : (E n).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
                have hsub : (E n) ⊆ ⋃ n ∈ Finset.range N, E n := Set.subset_biUnion_of_mem hn
                rw [h_empty_union] at hsub
                obtain ⟨x, hx⟩ := hnonempty
                exact Set.notMem_empty x (hsub hx)
              apply Finset.sum_eq_zero
              intro n hn
              rw [h_all_empty n hn, Lebesgue_measure.empty]
            rw [h_sum_zero, zero_add]
          · -- Both parts are nonempty compact and disjoint
            have h_nonempty_N : (E N).Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty_N
            have h_nonempty_union : (⋃ n ∈ Finset.range N, E n).Nonempty :=
              Set.nonempty_iff_ne_empty.mpr h_empty_union
            have h_sep : set_dist (⋃ n ∈ Finset.range N, E n) (E N) > 0 :=
              dist_of_disj_compact_pos _ _ h_nonempty_union h_nonempty_N hcompact_finite (hcompact N) h_disj_parts
            have h_add := Lebesgue_outer_measure.union_of_separated hd h_sep
            -- h_add : Lebesgue_outer_measure (...) = Lebesgue_outer_measure (...) + Lebesgue_outer_measure (E N)
            -- Since Lebesgue_measure = Lebesgue_outer_measure, we can use this directly
            calc Lebesgue_measure ((⋃ n ∈ Finset.range N, E n) ∪ E N)
                = Lebesgue_outer_measure ((⋃ n ∈ Finset.range N, E n) ∪ E N) := rfl
              _ = Lebesgue_outer_measure (⋃ n ∈ Finset.range N, E n) + Lebesgue_outer_measure (E N) := h_add
              _ = Lebesgue_measure (⋃ n ∈ Finset.range N, E n) + Lebesgue_measure (E N) := rfl
              _ = ∑ n ∈ Finset.range N, Lebesgue_measure (E n) + Lebesgue_measure (E N) := by rw [ih]
              _ = ∑ n ∈ Finset.range (N + 1), Lebesgue_measure (E n) := by rw [Finset.sum_range_succ]
    -- Now: ∑' m(E_n) = sup_N ∑_{n < N} m(E_n) ≤ sup_N m(⋃_{n < N} E_n) ≤ m(⋃ E_n)
    have h_mono : ∀ N : ℕ, (⋃ n ∈ Finset.range N, E n) ⊆ (⋃ n, E n) := by
      intro N x hx
      simp only [Set.mem_iUnion, Finset.mem_range] at hx ⊢
      obtain ⟨n, ⟨_, hxn⟩⟩ := hx
      exact ⟨n, hxn⟩
    have h_sum_le : ∀ N : ℕ, ∑ n ∈ Finset.range N, Lebesgue_measure (E n) ≤
        Lebesgue_measure (⋃ n, E n) := by
      intro N
      rw [← h_finite_sum N]
      exact Lebesgue_outer_measure.mono (h_mono N)
    -- All measures are nonnegative (by definition of outer measure)
    have h_nn : ∀ n, 0 ≤ Lebesgue_measure (E n) := fun _ => Lebesgue_outer_measure.nonneg _
    exact EReal.tsum_le_of_sum_range_le_of_nonneg h_nn h_sum_le
  exact le_antisymm h_le h_ge

/-- Helper: Countable additivity for bounded sets.
    Following the textbook approach: Use ε/2ⁿ trick with inner regularity (Exercise 1.2.7).
    For bounded measurable $`E_n`, find compact $`K_n ⊆ E_n` with $`m(E_n) ≤ m(K_n) + ε/2^(n+1)`.
    The $`K_n` are pairwise disjoint (since $`K_n ⊆ E_n`), so $`m(⋃ K_n) = ∑' m(K_n)` by compact case,
    and $`m(⋃ E_n) ≥ m(⋃ K_n) = ∑' m(K_n) ≥ ∑' m(E_n) - ε`. Let ε → 0. -/
private lemma Lebesgue_measure.countable_union_bounded {d:ℕ} (hd : 0 < d)
    {E: ℕ → Set (EuclideanSpace' d)}
    (hmes: ∀ n, LebesgueMeasurable (E n))
    (hbdd: ∀ n, Bornology.IsBounded (E n))
    (hdisj: Set.univ.PairwiseDisjoint E) :
    Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  -- Direction ≤: Countable subadditivity (always holds)
  have h_le : Lebesgue_measure (⋃ n, E n) ≤ ∑' n, Lebesgue_measure (E n) :=
    Lebesgue_outer_measure.union_le E
  -- Direction ≥: Use ε/2ⁿ trick with compact approximation
  have h_ge : ∑' n, Lebesgue_measure (E n) ≤ Lebesgue_measure (⋃ n, E n) := by
    -- Each bounded set has finite measure
    have h_finite : ∀ n, Lebesgue_measure (E n) ≠ ⊤ := by
      intro n
      have h_closure_compact : IsCompact (closure (E n)) :=
        Metric.isCompact_of_isClosed_isBounded isClosed_closure (hbdd n).closure
      have h_closure_finite : Lebesgue_measure (closure (E n)) ≠ ⊤ :=
        Lebesgue_outer_measure.finite_of_compact h_closure_compact
      have h_mono_closure : Lebesgue_measure (E n) ≤ Lebesgue_measure (closure (E n)) :=
        Lebesgue_outer_measure.mono subset_closure
      intro h_eq_top
      rw [h_eq_top] at h_mono_closure
      exact h_closure_finite (eq_top_iff.mpr h_mono_closure)
    -- Use ε-characterization: prove ∑' m(E_n) ≤ m(⋃ E_n) + ε for all ε > 0
    apply EReal.le_of_forall_pos_le_add'
    intro ε hε
    -- Extract TFAE condition (4): inner approximation by closed sets
    have h_TFAE := fun n => LebesgueMeasurable.TFAE (E n)
    -- Condition (1) → Condition (4): For measurable E, closed F ⊆ E with m(E \ F) ≤ δ
    have h_inner : ∀ n, ∀ δ > (0 : EReal), ∃ F : Set (EuclideanSpace' d),
        IsClosed F ∧ F ⊆ E n ∧ Lebesgue_outer_measure (E n \ F) ≤ δ := by
      intro n δ hδ
      have h_tfae := h_TFAE n
      -- TFAE gives us: (1) ↔ (4)
      -- Condition (1) is hmes n : LebesgueMeasurable (E n)
      -- Condition (4) is ∀ ε > 0, ∃ F closed, F ⊆ E, m(E \ F) ≤ ε
      have h_14 : LebesgueMeasurable (E n) →
          (∀ ε > 0, ∃ F : Set (EuclideanSpace' d), IsClosed F ∧ F ⊆ E n ∧
            Lebesgue_outer_measure (E n \ F) ≤ ε) := by
        have := List.TFAE.out h_tfae 1 4
        exact this.mp
      exact h_14 (hmes n) δ hδ
    -- Choose ε_n = ε / 2^{n+1} for each n
    -- For each n, get compact K_n ⊆ E_n with m(E_n) ≤ m(K_n) + ε/2^{n+1}
    have h_eps_pos : ∀ n, (0 : EReal) < ε / 2^(n+1) := by
      intro n
      have h_pow_pos : (0 : ℝ) < 2^(n+1) := by positivity
      have h_eps_over_pow : (0 : ℝ) < ε / 2^(n+1) := by positivity
      -- ε/2^(n+1) > 0 by straightforward calculation
      calc (0 : EReal) < (ε / 2^(n+1) : ℝ) := EReal.coe_pos.mpr h_eps_over_pow
        _ = (ε : EReal) / (2^(n+1) : ℝ) := by rw [EReal.coe_div]
        _ = (ε : EReal) / (2 : EReal)^(n+1) := by simp only [EReal.coe_pow]; rfl
    choose F hF using fun n => h_inner n (ε / 2^(n+1)) (h_eps_pos n)
    -- F_n is closed (from h_inner), bounded (since F_n ⊆ E_n and E_n bounded), hence compact
    have hF_compact : ∀ n, IsCompact (F n) := by
      intro n
      have hF_closed : IsClosed (F n) := (hF n).1
      have hF_bdd : Bornology.IsBounded (F n) :=
        Bornology.IsBounded.subset (hbdd n) (hF n).2.1
      exact Metric.isCompact_of_isClosed_isBounded hF_closed hF_bdd
    -- F_n are pairwise disjoint (since F_n ⊆ E_n and E_n are pairwise disjoint)
    have hF_disj : Set.univ.PairwiseDisjoint F := by
      intro i _ j _ hij
      have hE_disj : Disjoint (E i) (E j) := hdisj (Set.mem_univ i) (Set.mem_univ j) hij
      exact Set.disjoint_of_subset_left (hF i).2.1 (Set.disjoint_of_subset_right (hF j).2.1 hE_disj)
    -- By the compact case: m(⋃ F_n) = ∑' m(F_n)
    have h_compact_case : Lebesgue_measure (⋃ n, F n) = ∑' n, Lebesgue_measure (F n) :=
      Lebesgue_measure.countable_union_compact hd hF_compact hF_disj
    -- Key inequality: m(E_n) ≤ m(F_n) + ε/2^{n+1}
    have h_approx : ∀ n, Lebesgue_measure (E n) ≤ Lebesgue_measure (F n) + ε / 2^(n+1) := by
      intro n
      -- E_n = F_n ∪ (E_n \ F_n), and F_n ⊆ E_n
      -- By monotonicity and subadditivity: m(E_n) ≤ m(F_n) + m(E_n \ F_n) ≤ m(F_n) + ε/2^{n+1}
      have h_partition : E n = F n ∪ (E n \ F n) := (Set.union_diff_cancel (hF n).2.1).symm
      -- Binary subadditivity: m(A ∪ B) ≤ m(A) + m(B)
      have h_binary_subadd : Lebesgue_measure (F n ∪ (E n \ F n)) ≤
          Lebesgue_measure (F n) + Lebesgue_measure (E n \ F n) := by
        -- Use finite_union_le with Fin 2
        let S : Fin 2 → Set (EuclideanSpace' d) := ![F n, E n \ F n]
        have h_eq : F n ∪ (E n \ F n) = ⋃ i : Fin 2, S i := by
          ext x
          simp only [Set.mem_union, Set.mem_iUnion, S]
          constructor
          · intro h
            cases h with
            | inl hF => exact ⟨0, by simp [hF]⟩
            | inr hDiff => exact ⟨1, by simp [hDiff]⟩
          · intro ⟨i, hi⟩
            fin_cases i
            · left; exact hi
            · right; exact hi
        rw [h_eq]
        calc Lebesgue_measure (⋃ i : Fin 2, S i)
            ≤ ∑ i : Fin 2, Lebesgue_outer_measure (S i) := Lebesgue_outer_measure.finite_union_le S
          _ = Lebesgue_outer_measure (S 0) + Lebesgue_outer_measure (S 1) := Fin.sum_univ_two _
          _ = Lebesgue_measure (F n) + Lebesgue_measure (E n \ F n) := by simp only [S]; rfl
      calc Lebesgue_measure (E n) = Lebesgue_measure (F n ∪ (E n \ F n)) := by
            conv_lhs => rw [h_partition]
        _ ≤ Lebesgue_measure (F n) + Lebesgue_measure (E n \ F n) := h_binary_subadd
        _ ≤ Lebesgue_measure (F n) + ε / 2^(n+1) := by
          apply add_le_add_right
          exact (hF n).2.2
    -- Sum the approximations: ∑' m(E_n) ≤ ∑' m(F_n) + ∑' (ε/2^{n+1}) = ∑' m(F_n) + ε
    have h_sum_eps : ∑' n, (ε / (2 : EReal)^(n+1)) = ε := by
      -- ∑_{n=0}^∞ ε/2^{n+1} = ε · ∑_{n=0}^∞ 1/2^{n+1} = ε · 1 = ε
      -- First show (2 : EReal)^k = ((2^k : ℝ) : EReal) by induction
      have h2_eq : ∀ k : ℕ, (2 : EReal) ^ k = ((2 ^ k : ℝ) : EReal) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => simp only [pow_succ]; rw [ih]; push_cast; rfl
      -- Show EReal division equals Real division coerced
      have h_eq : ∀ n, (ε : EReal) / (2 : EReal) ^ (n + 1) = ((ε / (2 : ℝ)^(n+1)) : ℝ) := fun n => by
        rw [h2_eq (n + 1), ← EReal.coe_div]
      -- Summability and non-negativity for Real series
      have h_nn : ∀ n, 0 ≤ ε / (2 : ℝ)^(n+1) := fun n => by positivity
      have h_sum : Summable (fun n => ε / (2 : ℝ)^(n+1)) := by
        have h_eq_fn : (fun n => ε / (2 : ℝ)^(n+1)) = (fun n => ε/2 * (1/2 : ℝ)^n) := by
          ext n
          have h2 : (2 : ℝ) ^ (n+1) = 2 * 2^n := by ring
          field_simp [h2]; ring_nf; simp
        rw [h_eq_fn]
        exact summable_geometric_two.mul_left (ε/2)
      simp_rw [h_eq, ← EReal.coe_tsum_of_nonneg h_nn h_sum, tsum_geometric_eps ε hε]
    -- ∑' m(E_n) ≤ ∑' m(F_n) + ε
    have h_tsum_approx : ∑' n, Lebesgue_measure (E n) ≤ ∑' n, Lebesgue_measure (F n) + ε := by
      -- Lift to ENNReal where tsum_le_tsum and tsum_add work cleanly
      let mE_enn : ℕ → ENNReal := fun n => (Lebesgue_measure (E n)).toENNReal
      let mF_enn : ℕ → ENNReal := fun n => (Lebesgue_measure (F n)).toENNReal
      let eps_enn : ℕ → ENNReal := fun n => ((ε : EReal) / 2 ^ (n + 1)).toENNReal
      have h_mE_nn : ∀ n, 0 ≤ Lebesgue_measure (E n) := fun n => Lebesgue_outer_measure.nonneg (E n)
      have h_mF_nn : ∀ n, 0 ≤ Lebesgue_measure (F n) := fun n => Lebesgue_outer_measure.nonneg (F n)
      have h_eps_nn : ∀ n, (0 : EReal) ≤ (ε : EReal) / 2 ^ (n + 1) := fun n => le_of_lt (h_eps_pos n)
      -- Coerce back: x = x.toENNReal for non-negative EReal
      have h_mE_coe : ∀ n, Lebesgue_measure (E n) = (mE_enn n : EReal) := fun n =>
        (EReal.coe_toENNReal (h_mE_nn n)).symm
      have h_mF_coe : ∀ n, Lebesgue_measure (F n) = (mF_enn n : EReal) := fun n =>
        (EReal.coe_toENNReal (h_mF_nn n)).symm
      have h_eps_coe : ∀ n, (ε : EReal) / 2 ^ (n + 1) = (eps_enn n : EReal) := fun n =>
        (EReal.coe_toENNReal (h_eps_nn n)).symm
      -- In ENNReal: h_approx gives mE_enn n ≤ mF_enn n + eps_enn n
      have h_approx_enn : ∀ n, mE_enn n ≤ mF_enn n + eps_enn n := by
        intro n
        have h := h_approx n
        rw [h_mE_coe, h_mF_coe, h_eps_coe] at h
        rw [← EReal.coe_ennreal_add] at h
        exact EReal.coe_ennreal_le_coe_ennreal_iff.mp h
      -- ENNReal tsum_le_tsum: ∑' mE_enn ≤ ∑' (mF_enn + eps_enn)
      have h_tsum_le : ∑' n, mE_enn n ≤ ∑' n, (mF_enn n + eps_enn n) :=
        ENNReal.tsum_le_tsum h_approx_enn
      -- ENNReal tsum_add: ∑' (mF_enn + eps_enn) = ∑' mF_enn + ∑' eps_enn
      have h_tsum_add : ∑' n, (mF_enn n + eps_enn n) = ∑' n, mF_enn n + ∑' n, eps_enn n :=
        ENNReal.tsum_add
      -- Coerce back to EReal
      simp_rw [h_mE_coe, h_mF_coe]
      -- Use continuous coercion to lift tsum results
      have h_cont : Continuous (fun x : ENNReal => (x : EReal)) := continuous_coe_ennreal_ereal
      let φ : ENNReal →+ EReal := {
        toFun := (↑·)
        map_zero' := rfl
        map_add' := EReal.coe_ennreal_add
      }
      have h_tsum_mE : ∑' n, (mE_enn n : EReal) = φ (∑' n, mE_enn n) :=
        (Summable.map_tsum ENNReal.summable φ h_cont).symm
      have h_tsum_mF : ∑' n, (mF_enn n : EReal) = φ (∑' n, mF_enn n) :=
        (Summable.map_tsum ENNReal.summable φ h_cont).symm
      have h_tsum_eps : ∑' n, (eps_enn n : EReal) = φ (∑' n, eps_enn n) :=
        (Summable.map_tsum ENNReal.summable φ h_cont).symm
      rw [h_tsum_mE, h_tsum_mF]
      -- Show φ (∑' mE_enn) ≤ φ (∑' mF_enn) + ε
      calc φ (∑' n, mE_enn n)
          ≤ φ (∑' n, (mF_enn n + eps_enn n)) := by
            apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr h_tsum_le
        _ = φ (∑' n, mF_enn n + ∑' n, eps_enn n) := by rw [h_tsum_add]
        _ = φ (∑' n, mF_enn n) + φ (∑' n, eps_enn n) := φ.map_add _ _
        _ = φ (∑' n, mF_enn n) + ∑' n, (eps_enn n : EReal) := by rw [← h_tsum_eps]
        _ = φ (∑' n, mF_enn n) + ∑' n, (ε : EReal) / 2 ^ (n + 1) := by simp_rw [← h_eps_coe]
        _ = φ (∑' n, mF_enn n) + ε := by rw [h_sum_eps]
    -- m(⋃ F_n) ≤ m(⋃ E_n) by monotonicity (since F_n ⊆ E_n)
    have h_union_mono : Lebesgue_measure (⋃ n, F n) ≤ Lebesgue_measure (⋃ n, E n) := by
      apply Lebesgue_outer_measure.mono
      apply Set.iUnion_mono
      intro n
      exact (hF n).2.1
    -- Combine: ∑' m(E_n) ≤ ∑' m(F_n) + ε = m(⋃ F_n) + ε ≤ m(⋃ E_n) + ε
    calc ∑' n, Lebesgue_measure (E n)
        ≤ ∑' n, Lebesgue_measure (F n) + ε := h_tsum_approx
      _ = Lebesgue_measure (⋃ n, F n) + ε := by rw [h_compact_case]
      _ ≤ Lebesgue_measure (⋃ n, E n) + ε := add_le_add_left h_union_mono ε
  exact le_antisymm h_le h_ge

/-- Lemma 1.2.15(b) (Countable additivity).
    Strategy: `m(⋃ E_n) = ∑' m(E_n)` for pairwise disjoint measurable sets.
    - Direction ≤: Countable subadditivity ({name}`Lebesgue_outer_measure.union_le`)
    - Direction ≥: Decompose ℝᵈ into annuli Aₘ, express each `E_n = ⋃_m (E_n ∩ Aₘ)`,
      apply bounded case to the doubly-indexed family $`(E_n ∩ Aₘ)`. -/
theorem Lebesgue_measure.countable_union {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hmes: ∀ n, LebesgueMeasurable (E n)) (hdisj: Set.univ.PairwiseDisjoint E) : Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  -- Direction ≤: Countable subadditivity
  have h_le : Lebesgue_measure (⋃ n, E n) ≤ ∑' n, Lebesgue_measure (E n) :=
    Lebesgue_outer_measure.union_le E
  -- Direction ≥: Use annuli decomposition for general case
  have h_ge : ∑' n, Lebesgue_measure (E n) ≤ Lebesgue_measure (⋃ n, E n) := by
    -- Handle d = 0 case separately (trivial)
    by_cases hd : d = 0
    · -- In dimension 0, the space is a singleton (Subsingleton), so any pairwise disjoint
      -- family has at most one nonempty set. The sum equals the measure of the union.
      subst hd
      haveI : Subsingleton (EuclideanSpace' 0) := inferInstance
      -- Each E n is either ∅ or univ (the singleton). For disjoint sets, at most one is nonempty.
      by_cases h_empty : ∀ n, E n = ∅
      · -- All sets are empty: both sides are 0
        simp_rw [h_empty, Set.iUnion_empty]
        simp only [Lebesgue_measure.empty, tsum_zero, le_refl]
      · -- At least one E n is nonempty; by disjointness in a subsingleton, exactly one
        push_neg at h_empty
        obtain ⟨n₀, hn₀⟩ := h_empty
        -- In a Subsingleton, a nonempty set equals univ
        have hE_univ : E n₀ = Set.univ := by
          ext x
          simp only [Set.mem_univ, iff_true]
          exact Subsingleton.mem_iff_nonempty.mpr hn₀
        -- All other E m must be empty (disjoint from E n₀ = univ)
        have hE_empty : ∀ m, m ≠ n₀ → E m = ∅ := by
          intro m hm
          have hdisj' : Disjoint (E n₀) (E m) := hdisj (Set.mem_univ n₀) (Set.mem_univ m) hm.symm
          rw [hE_univ, Set.disjoint_iff] at hdisj'
          ext x
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hx
          have : x ∈ Set.univ ∩ E m := ⟨Set.mem_univ x, hx⟩
          exact Set.notMem_empty x (hdisj' this)
        -- The union equals E n₀
        have h_union : (⋃ n, E n) = E n₀ := by
          ext x
          simp only [Set.mem_iUnion]
          constructor
          · intro ⟨n, hxn⟩
            by_cases hn : n = n₀
            · exact hn ▸ hxn
            · rw [hE_empty n hn] at hxn
              exact (Set.notMem_empty x hxn).elim
          · intro hx
            exact ⟨n₀, hx⟩
        -- The sum has only one nonzero term
        have h_sum : ∑' n, Lebesgue_measure (E n) = Lebesgue_measure (E n₀) := by
          apply tsum_eq_single n₀
          intro m hm
          rw [hE_empty m hm, Lebesgue_measure.empty]
        rw [h_sum, h_union]
    · -- For d ≥ 1, use the annuli decomposition from the textbook
      push_neg at hd
      have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
      -- Define annuli: A_m = { x : m ≤ |x| < m+1 } for m ≥ 0
      -- Then ℝᵈ = ⋃_m A_m (disjoint union) and each A_m is bounded
      let A : ℕ → Set (EuclideanSpace' d) := fun m =>
        { x | (m : ℝ) ≤ ‖x‖ ∧ ‖x‖ < m + 1 }
      -- Each annulus is bounded
      have hA_bdd : ∀ m, Bornology.IsBounded (A m) := by
        intro m
        rw [Metric.isBounded_iff_subset_closedBall 0]
        use m + 1
        intro x hx
        simp only [Metric.mem_closedBall, dist_zero_right, A, Set.mem_setOf_eq] at hx ⊢
        exact le_of_lt hx.2
      -- The annuli cover all of ℝᵈ
      have hA_cover : ∀ x : EuclideanSpace' d, ∃ m, x ∈ A m := by
        intro x
        use ⌊‖x‖⌋₊
        simp only [A, Set.mem_setOf_eq]
        constructor
        · exact Nat.floor_le (norm_nonneg x)
        · exact Nat.lt_floor_add_one ‖x‖
      -- The annuli are pairwise disjoint
      have hA_disj : Set.univ.PairwiseDisjoint A := by
        intro i _ j _ hij
        simp only [Function.onFun, Set.disjoint_iff]
        intro x ⟨hi, hj⟩
        simp only [A, Set.mem_setOf_eq, Set.mem_empty_iff_false] at hi hj ⊢
        by_cases h : i < j
        · have h1 : (j : ℝ) ≤ ‖x‖ := hj.1
          have h2 : ‖x‖ < i + 1 := hi.2
          have h3 : (j : ℝ) < i + 1 := lt_of_le_of_lt h1 h2
          have h4 : j < i + 1 := by exact_mod_cast h3
          omega
        · push_neg at h
          have hji : j < i := lt_of_le_of_ne h (Ne.symm hij)
          have h1 : (i : ℝ) ≤ ‖x‖ := hi.1
          have h2 : ‖x‖ < j + 1 := hj.2
          have h3 : (i : ℝ) < j + 1 := lt_of_le_of_lt h1 h2
          have h4 : i < j + 1 := by exact_mod_cast h3
          omega
      -- Define the doubly-indexed family E'(n,m) = E_n ∩ A_m
      let E' : ℕ × ℕ → Set (EuclideanSpace' d) := fun ⟨n, m⟩ => E n ∩ A m
      -- E' is measurable (intersection of measurable and Borel sets)
      have hE'_mes : ∀ p, LebesgueMeasurable (E' p) := by
        intro ⟨n, m⟩
        -- E n is measurable, A m is Borel (hence measurable)
        have hA_meas : LebesgueMeasurable (A m) := by
          -- A m = { x | m ≤ ‖x‖ } ∩ { x | ‖x‖ < m + 1 }
          -- { x | m ≤ ‖x‖ } is closed, { x | ‖x‖ < m + 1 } is open
          have h1 : IsClosed { x : EuclideanSpace' d | (m : ℝ) ≤ ‖x‖ } :=
            isClosed_le continuous_const continuous_norm
          have h2 : IsOpen { x : EuclideanSpace' d | ‖x‖ < (m : ℝ) + 1 } :=
            isOpen_lt continuous_norm continuous_const
          have heq : A m = { x | (m : ℝ) ≤ ‖x‖ } ∩ { x | ‖x‖ < (m : ℝ) + 1 } := by
            ext x; simp only [A, Set.mem_setOf_eq, Set.mem_inter_iff]
          rw [heq]
          exact LebesgueMeasurable.inter h1.measurable h2.measurable
        exact LebesgueMeasurable.inter (hmes n) hA_meas
      -- E' is bounded (subset of bounded A_m)
      have hE'_bdd : ∀ p, Bornology.IsBounded (E' p) := by
        intro ⟨n, m⟩
        exact Bornology.IsBounded.subset (hA_bdd m) Set.inter_subset_right
      -- E' is pairwise disjoint
      have hE'_disj : Set.univ.PairwiseDisjoint E' := by
        intro ⟨n₁, m₁⟩ _ ⟨n₂, m₂⟩ _ hne
        simp only [E', Function.onFun]
        by_cases hn : n₁ = n₂
        · -- Same n, different m: disjoint by annuli
          subst hn
          have hm : m₁ ≠ m₂ := by
            intro heq
            exact hne (Prod.ext rfl heq)
          have hA_disj' : Disjoint (A m₁) (A m₂) :=
            hA_disj (Set.mem_univ m₁) (Set.mem_univ m₂) hm
          exact Set.disjoint_of_subset_left Set.inter_subset_right
            (Set.disjoint_of_subset_right Set.inter_subset_right hA_disj')
        · -- Different n: disjoint by original family
          have hE_disj' : Disjoint (E n₁) (E n₂) :=
            hdisj (Set.mem_univ n₁) (Set.mem_univ n₂) hn
          exact Set.disjoint_of_subset_left Set.inter_subset_left
            (Set.disjoint_of_subset_right Set.inter_subset_left hE_disj')
      -- ⋃_n E_n = ⋃_p E' p (reindex the union)
      have h_union_eq : (⋃ n, E n) = ⋃ p, E' p := by
        ext x
        simp only [Set.mem_iUnion, E']
        constructor
        · intro ⟨n, hx⟩
          obtain ⟨m, hm⟩ := hA_cover x
          exact ⟨⟨n, m⟩, ⟨hx, hm⟩⟩
        · intro ⟨⟨n, m⟩, hx⟩
          exact ⟨n, hx.1⟩
      -- Apply countable_union_bounded to E' (reindexed as ℕ via equivalence ℕ × ℕ ≃ ℕ)
      -- Step 1: Reindex E' to E'' : ℕ → Set using Nat.pairEquiv
      let e := Nat.pairEquiv.symm  -- e : ℕ ≃ ℕ × ℕ
      let E'' : ℕ → Set (EuclideanSpace' d) := fun k => E' (e k)
      -- Step 2: E'' inherits measurability, boundedness, and disjointness
      have hE''_mes : ∀ k, LebesgueMeasurable (E'' k) := fun k => hE'_mes (e k)
      have hE''_bdd : ∀ k, Bornology.IsBounded (E'' k) := fun k => hE'_bdd (e k)
      have hE''_disj : Set.univ.PairwiseDisjoint E'' := by
        intro i _ j _ hij
        simp only [E'', Function.onFun]
        have hne : e i ≠ e j := by
          intro heq
          apply hij
          exact e.injective heq
        exact hE'_disj (Set.mem_univ (e i)) (Set.mem_univ (e j)) hne
      -- Step 3: The unions are equal
      have h_union_E'' : (⋃ p, E' p) = ⋃ k, E'' k := by
        ext x
        simp only [Set.mem_iUnion, E'']
        constructor
        · intro ⟨p, hp⟩
          use e.symm p
          simp [hp]
        · intro ⟨k, hk⟩
          use e k
      -- Step 4: Apply countable_union_bounded to E''
      have h_E''_eq : Lebesgue_measure (⋃ k, E'' k) = ∑' k, Lebesgue_measure (E'' k) :=
        Lebesgue_measure.countable_union_bounded hd_pos hE''_mes hE''_bdd hE''_disj
      -- Step 5: Relate sums: ∑' k, m(E'' k) = ∑' p, m(E' p) by reindexing
      have h_tsum_reindex : ∑' k, Lebesgue_measure (E'' k) = ∑' p, Lebesgue_measure (E' p) := by
        rw [show (∑' p, Lebesgue_measure (E' p)) = ∑' k, Lebesgue_measure (E' (e k)) from
          (Equiv.tsum_eq e (fun p => Lebesgue_measure (E' p))).symm]
      -- Step 6: Relate ∑' n, m(E n) to ∑' p, m(E' p)
      -- Each E n = ⋃ k, (E n ∩ A k) is a disjoint union of bounded measurable sets
      -- So m(E n) = ∑' k, m(E n ∩ A k) by countable_union_bounded
      have h_En_decomp : ∀ n, Lebesgue_measure (E n) = ∑' k, Lebesgue_measure (E n ∩ A k) := by
        intro n
        -- Define the family for fixed n
        let F : ℕ → Set (EuclideanSpace' d) := fun k => E n ∩ A k
        have hF_eq : E n = ⋃ k, F k := by
          ext x
          simp only [F, Set.mem_iUnion, Set.mem_inter_iff]
          constructor
          · intro hx
            obtain ⟨k, hk⟩ := hA_cover x
            exact ⟨k, hx, hk⟩
          · intro ⟨k, hx, _⟩
            exact hx
        have hF_mes : ∀ k, LebesgueMeasurable (F k) := fun k => hE'_mes (n, k)
        have hF_bdd : ∀ k, Bornology.IsBounded (F k) := fun k => hE'_bdd (n, k)
        have hF_disj : Set.univ.PairwiseDisjoint F := by
          intro k₁ _ k₂ _ hk
          simp only [F, Function.onFun]
          have hA_disj' : Disjoint (A k₁) (A k₂) :=
            hA_disj (Set.mem_univ k₁) (Set.mem_univ k₂) hk
          exact Set.disjoint_of_subset_right Set.inter_subset_right
            (Set.disjoint_of_subset_left Set.inter_subset_right hA_disj')
        calc Lebesgue_measure (E n)
            = Lebesgue_measure (⋃ k, F k) := by rw [hF_eq]
          _ = ∑' k, Lebesgue_measure (F k) :=
              Lebesgue_measure.countable_union_bounded hd_pos hF_mes hF_bdd hF_disj
          _ = ∑' k, Lebesgue_measure (E n ∩ A k) := rfl
      -- Step 7: Now relate the double sum to the product sum
      -- ∑' n, m(E n) = ∑' n, ∑' k, m(E n ∩ A k) = ∑' (n,k), m(E n ∩ A k) = ∑' p, m(E' p)
      have h_sum_eq : ∑' n, Lebesgue_measure (E n) = ∑' p, Lebesgue_measure (E' p) := by
        simp_rw [h_En_decomp]
        -- Need: ∑' n, ∑' k, m(E n ∩ A k) = ∑' p, m(E' p)
        -- Simplify the inner sums to use E'
        have h_eq : ∀ n k, Lebesgue_measure (E n ∩ A k) = Lebesgue_measure (E' (n, k)) := by
          intro n k; simp only [E']
        simp_rw [h_eq]
        -- Now need: ∑' n, ∑' k, m(E' (n, k)) = ∑' p, m(E' p)
        -- Lift to ENNReal where tsum_prod' works unconditionally
        -- Define ENNReal version: f_enn p = m(E' p).toENNReal
        let f_enn : ℕ × ℕ → ENNReal := fun p => (Lebesgue_measure (E' p)).toENNReal
        -- Lebesgue measure is non-negative, so toENNReal is well-defined
        have hf_nn : ∀ p, 0 ≤ Lebesgue_measure (E' p) := fun p => Lebesgue_outer_measure.nonneg (E' p)
        -- ENNReal.tsum_prod' gives: ∑' p, f_enn p = ∑' n, ∑' k, f_enn (n, k)
        have h_enn_prod : ∑' n, ∑' k, f_enn (n, k) = ∑' p, f_enn p := ENNReal.tsum_prod'.symm
        -- Coerce back to EReal: For non-negative EReal, x = (x.toENNReal : EReal)
        have h_coe : ∀ p, Lebesgue_measure (E' p) = (f_enn p : EReal) := by
          intro p
          simp only [f_enn]
          exact (EReal.coe_toENNReal (hf_nn p)).symm
        simp_rw [h_coe]
        -- Now need: ∑' n, ∑' k, (f_enn (n, k) : EReal) = ∑' p, (f_enn p : EReal)
        -- Use continuous coercion from ENNReal to EReal
        have h_cont : Continuous (fun x : ENNReal => (x : EReal)) := continuous_coe_ennreal_ereal
        -- Define coercion as AddMonoidHom
        let φ : ENNReal →+ EReal := {
          toFun := (↑·)
          map_zero' := rfl
          map_add' := EReal.coe_ennreal_add
        }
        -- Map tsum through coercion using Summable.map_tsum
        -- For ENNReal, Summable always holds
        have h_map_outer : ∑' p, (f_enn p : EReal) = φ (∑' p, f_enn p) :=
          (Summable.map_tsum ENNReal.summable φ h_cont).symm
        have h_map_inner : ∀ n, ∑' k, (f_enn (n, k) : EReal) = φ (∑' k, f_enn (n, k)) := by
          intro n
          exact (Summable.map_tsum ENNReal.summable φ h_cont).symm
        have h_map_double : ∑' n, φ (∑' k, f_enn (n, k)) = φ (∑' n, ∑' k, f_enn (n, k)) :=
          (Summable.map_tsum ENNReal.summable φ h_cont).symm
        simp_rw [h_map_inner]
        rw [h_map_double, h_map_outer, h_enn_prod]
      -- Final step: combine everything
      calc ∑' n, Lebesgue_measure (E n)
          = ∑' p, Lebesgue_measure (E' p) := h_sum_eq
        _ = ∑' k, Lebesgue_measure (E'' k) := h_tsum_reindex.symm
        _ = Lebesgue_measure (⋃ k, E'' k) := h_E''_eq.symm
        _ = Lebesgue_measure (⋃ p, E' p) := by rw [← h_union_E'']
        _ = Lebesgue_measure (⋃ n, E n) := by rw [← h_union_eq]
        _ ≤ Lebesgue_measure (⋃ n, E n) := le_refl _
  exact le_antisymm h_le h_ge

theorem Lebesgue_measure.finite_union {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hmes: ∀ n, LebesgueMeasurable (E n)) (hdisj: Set.univ.PairwiseDisjoint E) : Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  -- Strategy: Extend E to ℕ-indexed family by padding with empty sets, then use countable_union
  -- Define E' : ℕ → Set by E'(k) = E(k) if k < n, else ∅
  let E' : ℕ → Set (EuclideanSpace' d) := fun k =>
    if h : k < n then E ⟨k, h⟩ else ∅

  -- The union over Fin n equals the union over ℕ with E'
  have h_union : (⋃ i : Fin n, E i) = (⋃ k, E' k) := by
    ext x
    simp only [Set.mem_iUnion, E']
    constructor
    · intro ⟨i, hi⟩
      use i.val
      simp [hi]
    · intro ⟨k, hx⟩
      by_cases hk : k < n
      · use ⟨k, hk⟩
        simpa [dif_pos hk] using hx
      · simp [dif_neg hk] at hx

  -- E' is measurable (E(k) is measurable, ∅ is measurable)
  have hmes' : ∀ k, LebesgueMeasurable (E' k) := by
    intro k
    simp only [E']
    by_cases hk : k < n
    · simp [dif_pos hk]
      exact hmes ⟨k, hk⟩
    · simp [dif_neg hk]
      exact LebesgueMeasurable.empty

  -- E' is pairwise disjoint
  have hdisj' : Set.univ.PairwiseDisjoint E' := by
    intro i _ j _ hij
    simp only [E', Function.onFun]
    by_cases hi : i < n <;> by_cases hj : j < n
    · simp only [dif_pos hi, dif_pos hj]
      have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
        intro heq
        apply hij
        exact congrArg Fin.val heq
      exact hdisj (Set.mem_univ _) (Set.mem_univ _) hne
    · simp only [dif_pos hi, dif_neg hj]
      exact disjoint_bot_right
    · simp only [dif_neg hi, dif_pos hj]
      exact disjoint_bot_left
    · simp only [dif_neg hi, dif_neg hj]
      exact disjoint_bot_left

  -- Apply countable_union
  rw [h_union, Lebesgue_measure.countable_union hmes' hdisj']

  -- The tsum over ℕ equals the tsum over Fin n (since E' k = ∅ for k ≥ n)
  have h_empty : ∀ k ≥ n, E' k = ∅ := fun k hk => dif_neg (not_lt.mpr hk)
  have h_measure_empty : ∀ k ≥ n, Lebesgue_measure (E' k) = 0 := by
    intro k hk
    rw [h_empty k hk, Lebesgue_measure.empty]

  -- Convert tsum over ℕ to tsum over Fin n
  -- Key: E' k = E ⟨k, h⟩ for k < n, and E' k = ∅ for k ≥ n

  -- Direct approach: show term-by-term equality using the embedding
  have h_eq_terms : ∀ i : Fin n, Lebesgue_measure (E' i.val) = Lebesgue_measure (E i) := by
    intro i
    simp only [E', dif_pos i.isLt]

  -- The tsum over ℕ equals the tsum over Fin n via reindexing
  -- Show that the support of E' is contained in {k : k < n}
  have h_support : Function.support (fun k => Lebesgue_measure (E' k)) ⊆ Set.Iio n := by
    intro k hk
    simp only [Set.mem_Iio]
    contrapose! hk
    simp only [Function.mem_support, not_not]
    exact h_measure_empty k hk
  -- Reindex from ℕ to Set.Iio n
  rw [← tsum_subtype_eq_of_support_subset h_support]
  -- Define equivalence between ↑(Set.Iio n) and Fin n
  let e : ↑(Set.Iio n) ≃ Fin n := {
    toFun := fun ⟨k, hk⟩ => ⟨k, Set.mem_Iio.mp hk⟩
    invFun := fun i => ⟨i.val, Set.mem_Iio.mpr i.isLt⟩
    left_inv := fun ⟨k, hk⟩ => rfl
    right_inv := fun i => rfl
  }
  -- Use the equivalence to reindex the tsum
  rw [← Equiv.tsum_eq e]
  congr 1
  ext ⟨k, hk⟩
  simp only [e, Equiv.coe_fn_mk]
  exact h_eq_terms ⟨k, Set.mem_Iio.mp hk⟩

theorem Lebesgue_measure.union {d:ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) (hdisj: E ∩ F = ∅) : Lebesgue_measure (E ∪ F) = Lebesgue_measure E + Lebesgue_measure F := by
  -- Apply finite_union with n=2
  let S : Fin 2 → Set (EuclideanSpace' d) := ![E, F]
  have h_union : E ∪ F = ⋃ n, S n := by
    ext x
    simp only [S, Set.mem_union, Set.mem_iUnion]
    constructor
    · intro h
      cases h with
      | inl hl => exact ⟨0, hl⟩
      | inr hr => exact ⟨1, hr⟩
    · intro ⟨n, hn⟩
      fin_cases n
      · left; exact hn
      · right; exact hn
  have hmes : ∀ n, LebesgueMeasurable (S n) := by intro n; fin_cases n <;> simp [S, hE, hF]
  have hdisj' : Set.univ.PairwiseDisjoint S := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simp only [S, Function.onFun]
      exact Set.disjoint_iff_inter_eq_empty.mpr hdisj
    · simp only [S, Function.onFun]
      exact Set.disjoint_iff_inter_eq_empty.mpr (Set.inter_comm F E ▸ hdisj)
    · exact (hij rfl).elim
  rw [h_union, Lebesgue_measure.finite_union hmes hdisj']
  rw [tsum_fintype]
  simp only [S, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem Bornology.IsBounded.inElementary {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : ∃ (A: Set (EuclideanSpace' d)), IsElementary A ∧ E ⊆ A :=
  IsElementary.contains_bounded hE

