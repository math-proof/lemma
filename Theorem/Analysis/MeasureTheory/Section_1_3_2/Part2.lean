import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Def.Analysis.MeasureTheory.Section_1_3_2.Part2
set_option doc.verso.suggestions false


namespace UnsignedMeasurable.TFAE_helpers

variable {d : ℕ} {f : EuclideanSpace' d → EReal}

-- The limsup set is Lebesgue measurable when each g_n is a simple function
private lemma limsupSet_LebesgueMeasurable {g : ℕ → EuclideanSpace' d → EReal}
    (hg : ∀ n, UnsignedSimpleFunction (g n)) (t : EReal) :
    LebesgueMeasurable (limsupSet g t) := by
  apply LebesgueMeasurable.countable_union
  intro M
  apply LebesgueMeasurable.countable_inter
  intro N
  apply LebesgueMeasurable.countable_union
  intro n
  by_cases hn : n ≥ N
  · convert UnsignedSimpleFunction.levelset_gt_LebesgueMeasurable (hg n) (t + 1 / (M + 1))
    ext x; simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, and_iff_right_iff_imp]; intro _; exact hn
  · convert LebesgueMeasurable.empty
    ext x; simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro h; exact absurd h hn

-- This is the main technical work of the proof
private lemma iii_imp_v : stmt_iii f → stmt_v f := by
  intro ⟨g, hg_simple, hg_ae_conv⟩ t
  -- The null set where convergence fails
  let N := {x | ¬Filter.atTop.Tendsto (fun n ↦ g n x) (nhds (f x))}
  have hN_null : IsNull N := hg_ae_conv
  -- The limsup set E
  let E := limsupSet g t
  have hE_meas : LebesgueMeasurable E := limsupSet_LebesgueMeasurable hg_simple t
  -- Show {f > t} ∩ Nᶜ = E ∩ Nᶜ (they agree where convergence holds)
  -- The key insight: f(x) = lim g_n(x) = lim sup g_n(x) a.e.
  -- So {f > λ} = ⋃_{M≥1} ⋂_{N≥1} ⋃_{n≥N} {g_n > λ + 1/M} outside a null set
  have h_ae_eq : {x | f x > t} ∩ Nᶜ = E ∩ Nᶜ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, N]
    push_neg
    constructor
    · -- f x > t ∧ converges → x ∈ E ∧ converges
      intro ⟨hfx, hconv⟩
      refine ⟨?_, hconv⟩
      -- Since f(x) > t and g_n(x) → f(x), we can find M such that f(x) > t + 1/M
      -- Then eventually g_n(x) > t + 1/M, which means x ∈ limsupSet
      simp only [E, limsupSet, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq]
      -- The detailed analysis argument uses Filter.Tendsto properties
      -- For a limit f(x), if f(x) > t, then ∃ε>0 with f(x) > t+ε
      -- Choose M with 1/M < ε, then eventually g_n(x) > t + 1/M

      -- Case 1: t = ⊥
      rcases eq_bot_or_bot_lt t with rfl | ht_ne_bot
      · -- t = ⊥: threshold = ⊥ + eps = ⊥ for any M, and g n x > ⊥ since g n x ≥ 0
        use 0
        intro N
        use N, le_refl N
        simp only [EReal.bot_add, gt_iff_lt]
        -- g N x ≥ 0 > ⊥
        have hg_nonneg : g N x ≥ 0 := by
          obtain ⟨k, c, E, hE_props, heq⟩ := hg_simple N
          rw [heq]
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          apply Finset.sum_nonneg
          intro i _
          apply mul_nonneg (hE_props i).2
          simp only [EReal.indicator, Real.EReal_fun]
          exact EReal.coe_nonneg.mpr (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
        calc (⊥ : EReal) < 0 := EReal.bot_lt_zero
             _ ≤ g N x := hg_nonneg
      -- Case 2: f x = ⊤
      rcases eq_top_or_lt_top (f x) with hfx_top | hfx_lt_top
      · -- f x = ⊤: g_n → ⊤, so eventually g_n x > any threshold
        use 0
        intro N
        -- Since f x = ⊤ and f x > t, we have t < ⊤
        have ht_lt_top' : t < ⊤ := lt_of_lt_of_eq hfx hfx_top
        -- Therefore t + 1 < ⊤ (since 1 is finite)
        have h_t1_lt_top : t + 1 < ⊤ := EReal.add_lt_top (ne_top_of_lt ht_lt_top') (EReal.coe_ne_top 1)
        -- Show g n x > t + 1 for some n ≥ N using that g n → ⊤
        rw [hfx_top] at hconv
        -- Set.Ioi (t + 1) is a neighborhood of ⊤
        have h_mem : Set.Ioi (t + 1) ∈ nhds (⊤ : EReal) := Ioi_mem_nhds h_t1_lt_top
        have h_event : ∀ᶠ n in Filter.atTop, g n x ∈ Set.Ioi (t + 1) := hconv h_mem
        rw [Filter.eventually_atTop] at h_event
        obtain ⟨N₀, hN₀⟩ := h_event
        use max N₀ N, le_max_right _ _
        have h_n_mem := hN₀ (max N₀ N) (le_max_left _ _)
        simp only [Set.mem_Ioi, Nat.cast_zero, zero_add, gt_iff_lt] at h_n_mem ⊢
        calc t + 1 / 1 = t + 1 := by rw [div_one]
             _ < g (max N₀ N) x := h_n_mem
      -- Case 3: t < ⊤ and f x < ⊤, both are finite or f x > t means t < f x < ⊤
      rcases eq_top_or_lt_top t with rfl | ht_lt_top
      · -- t = ⊤: but hfx says f x > ⊤, impossible
        exfalso; exact (not_lt.mpr le_top) hfx
      -- Now ⊥ < t < ⊤ and f x > t, with f x < ⊤
      -- f x is finite since f x < ⊤ and f x > t > ⊥
      have hfx_ne_top : f x ≠ ⊤ := ne_top_of_lt hfx_lt_top
      have hfx_ne_bot : f x ≠ ⊥ := by
        intro h_eq_bot
        rw [h_eq_bot] at hfx
        exact not_lt_bot hfx
      have ht_ne_top : t ≠ ⊤ := ne_top_of_lt ht_lt_top
      have ht_ne_bot' : t ≠ ⊥ := ne_of_gt ht_ne_bot
      -- Extract real numbers
      obtain ⟨f', hf'⟩ : ∃ f' : ℝ, (f' : EReal) = f x := ⟨(f x).toReal, EReal.coe_toReal hfx_ne_top hfx_ne_bot⟩
      obtain ⟨t', ht'⟩ : ∃ t' : ℝ, (t' : EReal) = t := ⟨t.toReal, EReal.coe_toReal ht_ne_top ht_ne_bot'⟩
      -- Both f' and t' are real numbers with f' > t'
      have hf't' : f' > t' := by
        rw [← hf', ← ht'] at hfx
        exact EReal.coe_lt_coe_iff.mp hfx
      have hgap_pos : f' - t' > 0 := sub_pos.mpr hf't'
      -- Find M such that 1/(M+1) < f' - t'
      obtain ⟨M, hM⟩ := exists_nat_gt (1 / (f' - t'))
      use M
      intro N
      -- Show t' + 1/(M+1) < f'
      have h_lt : (t' : EReal) + 1 / ((M : EReal) + 1) < f' := by
        have hM1_pos : (M : ℝ) + 1 > 0 := by positivity
        have h1 : (1 : ℝ) / (M + 1) < f' - t' := by
          calc (1 : ℝ) / (M + 1) < 1 / (1 / (f' - t')) := by
                 apply div_lt_div_of_pos_left
                 · norm_num
                 · rw [one_div_pos]; exact hgap_pos
                 · calc 1 / (f' - t') < M := hM
                        _ < M + 1 := by exact_mod_cast Nat.lt_succ_self M
               _ = f' - t' := one_div_one_div (f' - t')
        have h2 : t' + 1 / (M + 1) < f' := by linarith
        -- Coerce to EReal
        have h_coe : ((t' : EReal) + 1 / ((M : EReal) + 1)) = ((t' + 1 / (M + 1) : ℝ) : EReal) := by
          rw [EReal.coe_add, EReal.coe_div]
          simp only [EReal.coe_one, EReal.coe_add, EReal.coe_natCast]
        rw [h_coe]
        exact EReal.coe_lt_coe_iff.mpr h2

      -- By convergence, eventually g_n(x) > t' + 1/(M+1)
      have h_event : ∀ᶠ n in Filter.atTop, g n x > (t' : EReal) + 1 / ((M : EReal) + 1) := by
        have h_mem : Set.Ioi ((t' : EReal) + 1 / ((M : EReal) + 1)) ∈ nhds (f x) := by
          rw [← hf']
          exact Ioi_mem_nhds h_lt
        exact hconv h_mem
      rw [Filter.eventually_atTop] at h_event
      obtain ⟨N₀, hN₀⟩ := h_event
      refine ⟨max N₀ N, le_max_right _ _, ?_⟩
      rw [← ht']
      exact hN₀ _ (le_max_left _ _)
    · -- x ∈ E ∧ converges → f x > t ∧ converges
      intro ⟨hE_mem, hconv⟩
      refine ⟨?_, hconv⟩
      -- If x ∈ limsupSet g t, then for some M, infinitely often g_n(x) > t + 1/M
      -- Since g_n(x) → f(x), limsup g_n(x) = f(x), so f(x) ≥ t + 1/M > t
      simp only [E, limsupSet, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq] at hE_mem
      -- hE_mem : ∃ M, ∀ N, ∃ n ≥ N, g n x > t + 1/(M+1)
      obtain ⟨M, hM⟩ := hE_mem
      -- Set threshold := t + 1/(M+1)
      set threshold := t + 1 / ((M : EReal) + 1) with h_threshold
      -- Handle edge cases first
      rcases eq_top_or_lt_top t with rfl | ht_ne_top
      · -- t = ⊤: threshold = ⊤ + eps = ⊤, and hM says g n x > ⊤, impossible
        exfalso
        obtain ⟨n, _, hn_gt⟩ := hM 0
        have h_threshold_eq_top : threshold = ⊤ := by
          rw [h_threshold]
          apply EReal.top_add_of_ne_bot
          intro h_eq
          have h_denom_ne_top : (M : EReal) + 1 ≠ ⊤ := EReal.add_ne_top (EReal.natCast_ne_top M) (EReal.coe_ne_top 1)
          have h_pos : (0 : EReal) < 1 / ((M : EReal) + 1) := by
            apply EReal.div_pos (EReal.coe_pos.mpr one_pos)
            calc (0 : EReal) < 1 := EReal.coe_pos.mpr one_pos
                 _ ≤ (M : EReal) + 1 := le_add_of_nonneg_left (EReal.coe_nonneg.mpr (Nat.cast_nonneg M))
            exact h_denom_ne_top
          rw [h_eq] at h_pos
          exact not_lt_bot h_pos
        rw [h_threshold_eq_top] at hn_gt
        exact (not_lt.mpr le_top) hn_gt
      rcases eq_bot_or_bot_lt t with rfl | ht_ne_bot
      · -- t = ⊥: threshold = ⊥ + eps = ⊥, need to show f x > ⊥
        -- Since g_n(x) ≥ 0 and g_n(x) → f(x), we have f(x) ≥ 0 > ⊥
        have hg_nonneg : ∀ n, g n x ≥ 0 := fun n => by
          obtain ⟨k, c, E, hE_props, heq⟩ := hg_simple n
          rw [heq]
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          apply Finset.sum_nonneg
          intro i _
          apply mul_nonneg (hE_props i).2
          simp only [EReal.indicator, Real.EReal_fun]
          exact EReal.coe_nonneg.mpr (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
        -- g n x ≥ 0 for all n, and g n x → f x, so f x ≥ 0
        have h_limit_nonneg : f x ≥ 0 := by
          by_contra h_neg
          push_neg at h_neg
          have h_mem : Set.Iio 0 ∈ nhds (f x) := Iio_mem_nhds h_neg
          have h_event : ∀ᶠ n in Filter.atTop, g n x < 0 := hconv h_mem
          rw [Filter.eventually_atTop] at h_event
          obtain ⟨N₀, hN₀⟩ := h_event
          have := hN₀ N₀ (le_refl _)
          exact (not_lt.mpr (hg_nonneg N₀)) this
        calc (⊥ : EReal) < 0 := EReal.bot_lt_zero
             _ ≤ f x := h_limit_nonneg
      -- Now ⊥ < t < ⊤ (t is a finite real)
      by_contra h_not_gt
      push_neg at h_not_gt
      -- h_not_gt : f x ≤ t
      -- Derive contradiction: if f x ≤ t, eventually g_n x < threshold, but frequently > threshold
      have h_denom_ne_top : (M : EReal) + 1 ≠ ⊤ := EReal.add_ne_top (EReal.natCast_ne_top M) (EReal.coe_ne_top 1)
      have h_eps_pos : (1 : EReal) / ((M : EReal) + 1) > 0 := by
        apply EReal.div_pos (EReal.coe_pos.mpr one_pos)
        calc (0 : EReal) < 1 := EReal.coe_pos.mpr one_pos
             _ ≤ (M : EReal) + 1 := le_add_of_nonneg_left (EReal.coe_nonneg.mpr (Nat.cast_nonneg M))
        exact h_denom_ne_top
      -- eps is finite: just use that eps > 0 is positive and less than or equal to 1
      -- (h_eps_ne_top is not needed for the proof below, we can skip this)
      -- t < threshold using add_lt_add for finite values
      have h_t_lt : t < threshold := by
        rw [h_threshold]
        -- t is finite, so we can work with coercions
        obtain ⟨t', rfl⟩ : ∃ t' : ℝ, (t' : EReal) = t := by
          induction t using EReal.rec with
          | bot => exact absurd rfl (ne_of_gt ht_ne_bot)
          | top => exact absurd rfl (ne_of_lt ht_ne_top)
          | coe r => exact ⟨r, rfl⟩
        conv_lhs => rw [← add_zero (t' : EReal)]
        exact EReal.add_lt_add_left_coe h_eps_pos t'
      -- f x < threshold
      have h_fx_lt : f x < threshold := lt_of_le_of_lt h_not_gt h_t_lt
      -- By convergence, eventually g_n x < threshold
      have h_event : ∀ᶠ n in Filter.atTop, g n x < threshold := hconv (Iio_mem_nhds h_fx_lt)
      rw [Filter.eventually_atTop] at h_event
      obtain ⟨N₀, hN₀⟩ := h_event
      -- But by hM, there exists n ≥ N₀ with g n x > threshold
      obtain ⟨n, hn_ge, hn_gt⟩ := hM N₀
      exact (lt_irrefl _) (lt_trans (hN₀ n hn_ge) hn_gt)
  exact LebesgueMeasurable.of_ae_eq hE_meas hN_null h_ae_eq

/-! # (v) ⟹ (vi): \{f ≥ λ\} = ⋂\_\{n≥1\} \{f > λ - 1/n\} -/

-- Helper: if x > n for all n ∈ ℕ, then x = ⊤
private lemma EReal.eq_top_of_forall_nat_lt {x : EReal} (h : ∀ n : ℕ, x > n) : x = ⊤ := by
  induction x using EReal.rec with
  | bot =>
    exfalso
    have h0 : (⊥ : EReal) > (0 : ℕ) := h 0
    simp only [Nat.cast_zero, gt_iff_lt, not_lt_bot] at h0
  | top => rfl
  | coe r =>
    exfalso
    have h1 : (r : EReal) > (⌈r⌉₊ : ℕ) := h ⌈r⌉₊
    have h1' : r > (⌈r⌉₊ : ℕ) := by
      simp only [gt_iff_lt] at h1 ⊢
      rwa [show ((⌈r⌉₊ : ℕ) : EReal) = ((⌈r⌉₊ : ℕ) : ℝ) by norm_cast,
           EReal.coe_lt_coe_iff] at h1
    have h2 : r ≤ ⌈r⌉₊ := Nat.le_ceil r
    linarith

private lemma v_imp_vi : stmt_v f → stmt_vi f := by
  intro hv t
  -- Handle cases based on t
  rcases eq_bot_or_bot_lt t with rfl | ht_bot
  · -- t = ⊥: {f ≥ ⊥} = Set.univ
    have h_eq : {x | f x ≥ ⊥} = Set.univ := by ext x; simp
    rw [h_eq, ← Set.compl_empty]
    exact LebesgueMeasurable.empty.complement
  rcases eq_top_or_lt_top t with rfl | ht_top
  · -- t = ⊤: {f ≥ ⊤} = {f = ⊤} = ⋂_{n ∈ ℕ} {f > n}
    have h_eq : {x | f x ≥ ⊤} = ⋂ (n : ℕ), {x | f x > n} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, ge_iff_le]
      constructor
      · intro hfx n
        simp only [gt_iff_lt, top_le_iff.mp hfx]
        apply EReal.coe_lt_top
      · intro hfx
        exact top_le_iff.mpr (EReal.eq_top_of_forall_nat_lt hfx)
    exact h_eq ▸ LebesgueMeasurable.countable_inter (fun n => hv _)
  · -- t is finite: use {f ≥ t} = ⋂_{n≥1} {f > t - 1/(n+1)}
    -- Since t < ⊤ and ⊥ < t, we know t is a real number
    induction t using EReal.rec with
    | bot => exact (not_lt.mpr le_rfl ht_bot).elim
    | top => exact (not_lt.mpr le_rfl ht_top).elim
    | coe t' =>
      -- Use {f ≥ t'} = ⋂_n {f > (t' - 1/(n+1) : ℝ)}
      have h_eq : {x | f x ≥ (t' : EReal)} = ⋂ (n : ℕ), {x | f x > ((t' - 1 / (n + 1)) : ℝ)} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iInter, ge_iff_le, gt_iff_lt]
        constructor
        · intro hfx n
          have h1 : (0 : ℝ) < 1 / (n + 1) := by positivity
          have h2 : (t' - 1 / (n + 1) : ℝ) < t' := by linarith
          have h3 : ((t' - 1 / (n + 1)) : EReal) < (t' : EReal) := EReal.coe_lt_coe_iff.mpr h2
          exact lt_of_lt_of_le h3 hfx
        · intro hfx
          by_contra h
          push_neg at h
          -- f x < t'
          have hfx_lt_t' : f x < (t' : EReal) := h
          -- Get a witness for f x being a real
          have hfx_ne_bot : f x ≠ ⊥ := by
            intro hfx_eq_bot
            have hbot : ((t' - 1 / ((0 : ℕ) + 1)) : ℝ) < (⊥ : EReal) := by
              simp only [Nat.cast_zero, zero_add, div_one]
              rw [← hfx_eq_bot]
              convert hfx 0 using 2
              simp
            exact not_lt_bot hbot
          have hfx_ne_top : f x ≠ ⊤ := ne_top_of_lt hfx_lt_t'
          -- So f x is a real
          have hr : f x = (f x).toReal := (EReal.coe_toReal hfx_ne_top hfx_ne_bot).symm
          set r := (f x).toReal with hr_def
          rw [hr] at hfx_lt_t' hfx
          have hr_lt_t' : r < t' := EReal.coe_lt_coe_iff.mp hfx_lt_t'
          have hdiff_pos : 0 < t' - r := by linarith
          obtain ⟨n, hn⟩ := exists_nat_gt (1 / (t' - r))
          have h_n_pos : (0 : ℝ) < n := by
            by_cases hn0 : n = 0
            · subst hn0; simp at hn; linarith
            · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
          have hn' : 1 / ((n : ℝ) + 1) < t' - r := by
            calc 1 / ((n : ℝ) + 1) < 1 / (n : ℝ) := by
                  apply one_div_lt_one_div_of_lt h_n_pos; linarith
              _ < 1 / (1 / (t' - r)) := by
                  apply one_div_lt_one_div_of_lt (one_div_pos.mpr hdiff_pos) hn
              _ = t' - r := one_div_one_div (t' - r)
          -- So (t' - 1/(n+1) : ℝ) > r
          have hcontra := hfx n
          have hcontra' := EReal.coe_lt_coe_iff.mp hcontra
          linarith
      rw [h_eq]
      exact LebesgueMeasurable.countable_inter (fun n => hv _)

/-! # (vi) ⟹ (v): \{f > λ\} = ⋃\_\{q ∈ ℚ, q > λ\} \{f ≥ q\} -/

private lemma vi_imp_v : stmt_vi f → stmt_v f := by
  intro hvi t
  -- {f > t} = ⋃_{q : ℚ, q > t} {f ≥ q}
  -- Since rationals are dense, for any x with f x > t, there exists q ∈ ℚ with t < q ≤ f x
  -- Use encoding of ℚ to ℕ for countable union (via Encodable ℚ)
  let F : ℕ → Set (EuclideanSpace' d) := fun n =>
    match @Encodable.decode ℚ _ n with
    | some q => if (t < ((q : ℝ) : EReal)) then {x | f x ≥ ((q : ℝ) : EReal)} else ∅
    | none => ∅
  have hF_eq : ∀ n, F n = match @Encodable.decode ℚ _ n with
    | some q => if (t < ((q : ℝ) : EReal)) then {x | f x ≥ ((q : ℝ) : EReal)} else ∅
    | none => ∅ := fun _ => rfl
  have h_eq : {x | f x > t} = ⋃ n, F n := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hfx
      -- f x > t, so there exists q ∈ ℚ with t < q < f x
      obtain ⟨q, hq1, hq2⟩ := EReal.exists_rat_btwn_of_lt hfx
      use Encodable.encode q  -- encode q as ℕ
      rw [hF_eq, Encodable.encodek]
      simp only [hq1, ite_true, Set.mem_setOf_eq]
      exact le_of_lt hq2
    · intro ⟨n, hn⟩
      rw [hF_eq] at hn
      cases hd : @Encodable.decode ℚ _ n with
      | none => simp only [hd, Set.mem_empty_iff_false] at hn
      | some q =>
        simp only [hd] at hn
        by_cases h : t < ((q : ℝ) : EReal)
        · simp only [h, ite_true, Set.mem_setOf_eq] at hn
          calc t < ((q : ℝ) : EReal) := h
            _ ≤ f x := hn
        · simp only [h, ite_false, Set.mem_empty_iff_false] at hn
  rw [h_eq]
  -- This is a countable union of measurable sets
  apply LebesgueMeasurable.countable_union
  intro n
  rw [hF_eq]
  cases hd : @Encodable.decode ℚ _ n with
  | none => exact LebesgueMeasurable.empty
  | some q =>
    simp only
    split_ifs with h
    · exact hvi ((q : ℝ) : EReal)
    · exact LebesgueMeasurable.empty

/-! # (v) ⟹ (viii): \{f ≤ t\} = \{f > t\}ᶜ -/

private lemma v_imp_viii : stmt_v f → stmt_viii f := by
  intro hv t
  have h_eq : {x | f x ≤ t} = {x | f x > t}ᶜ := by ext x; simp [not_lt]
  rw [h_eq]
  exact (hv t).complement

/-! # (vi) ⟹ (vii): \{f < t\} = \{f ≥ t\}ᶜ -/

private lemma vi_imp_vii : stmt_vi f → stmt_vii f := by
  intro hvi t
  have h_eq : {x | f x < t} = {x | f x ≥ t}ᶜ := by ext x; simp [not_le]
  rw [h_eq]
  exact (hvi t).complement

/-! # (vii) ⟹ (vi): \{f ≥ t\} = \{f < t\}ᶜ -/

private lemma vii_imp_vi : stmt_vii f → stmt_vi f := by
  intro hvii t
  have h_eq : {x | f x ≥ t} = {x | f x < t}ᶜ := by ext x; simp [not_lt]
  rw [h_eq]
  exact (hvii t).complement

/-! # (viii) ⟹ (v): \{f > t\} = \{f ≤ t\}ᶜ -/

private lemma viii_imp_v : stmt_viii f → stmt_v f := by
  intro hviii t
  have h_eq : {x | f x > t} = {x | f x ≤ t}ᶜ := by ext x; simp [not_le]
  rw [h_eq]
  exact (hviii t).complement

/-! # (v)-(viii) ⟹ (ix): Intervals are intersections of half-intervals -/

private lemma v_to_viii_imp_ix (hv : stmt_v f) (hvi : stmt_vi f) (hvii : stmt_vii f) (hviii : stmt_viii f) :
    stmt_ix f := by
  intro I
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Ioo a b) = {x | f x > a} ∩ {x | f x < b} := by
      rw [EReal.image_coe_Ioo]
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_inter_iff, Set.mem_setOf_eq, gt_iff_lt]
    rw [h_eq]
    exact (hv _).inter (hvii _)
  | Icc a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Icc a b) = {x | f x ≥ a} ∩ {x | f x ≤ b} := by
      rw [EReal.image_coe_Icc]
      ext x
      simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_inter_iff, Set.mem_setOf_eq, ge_iff_le]
    rw [h_eq]
    exact (hvi _).inter (hviii _)
  | Ioc a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Ioc a b) = {x | f x > a} ∩ {x | f x ≤ b} := by
      rw [EReal.image_coe_Ioc]
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_inter_iff, Set.mem_setOf_eq, gt_iff_lt]
    rw [h_eq]
    exact (hv _).inter (hviii _)
  | Ico a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Ico a b) = {x | f x ≥ a} ∩ {x | f x < b} := by
      rw [EReal.image_coe_Ico]
      ext x
      simp only [Set.mem_preimage, Set.mem_Ico, Set.mem_inter_iff, Set.mem_setOf_eq, ge_iff_le]
    rw [h_eq]
    exact (hvi _).inter (hvii _)

/-! # (ix) ⟹ (x): Open sets are countable unions of intervals -/

-- For unsigned f, f⁻¹'({⊥}) = ∅
private lemma unsigned_preimage_bot_empty (hf : Unsigned f) : f⁻¹' {⊥} = ∅ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  intro hfx
  have h := hf x
  rw [hfx] at h
  simp only [ge_iff_le] at h
  exact not_le.mpr EReal.bot_lt_zero h

-- The embedded reals ℝ as a subset of EReal
private lemma ereal_reals_eq_iUnion :
    (Set.range Real.toEReal : Set EReal) = ⋃ (n : ℕ), Real.toEReal '' Set.Ioo (-(n:ℝ) - 1) (n + 1) := by
  ext x
  simp only [Set.mem_range, Set.mem_iUnion, Set.mem_image, Set.mem_Ioo]
  constructor
  · intro ⟨r, hr⟩
    use ⌈|r|⌉₊, r
    constructor
    · constructor
      · have h1 : -|r| ≤ r := neg_abs_le r
        have h2 : |r| ≤ ⌈|r|⌉₊ := Nat.le_ceil |r|
        linarith
      · have h1 : r ≤ |r| := le_abs_self r
        have h2 : |r| ≤ ⌈|r|⌉₊ := Nat.le_ceil |r|
        linarith
    · exact hr
  · intro ⟨_, r, _, hr⟩
    exact ⟨r, hr⟩

-- ℝ embedded in EReal has Lebesgue measurable preimage
private lemma measurable_preimage_reals (hix : stmt_ix f) : LebesgueMeasurable (f⁻¹' (Set.range Real.toEReal)) := by
  rw [ereal_reals_eq_iUnion, Set.preimage_iUnion]
  apply LebesgueMeasurable.countable_union
  intro n
  exact hix (BoundedInterval.Ioo (-(n:ℝ) - 1) (n + 1))

-- {⊤} as complement of ℝ ∪ {⊥}
private lemma ereal_top_singleton_eq : ({⊤} : Set EReal) = (Set.range Real.toEReal ∪ {⊥})ᶜ := by
  ext x
  simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_union, Set.mem_range]
  constructor
  · intro hx
    rw [hx]
    push_neg
    constructor
    · intro r hr
      exact EReal.coe_ne_top r hr
    · intro h; exact absurd h.symm (ne_of_lt bot_lt_top)
  · intro hx
    push_neg at hx
    induction x using EReal.rec with
    | bot => exact (hx.2 rfl).elim
    | top => rfl
    | coe r => exact (hx.1 r rfl).elim

-- For unsigned f, f⁻¹'({⊤}) is Lebesgue measurable
private lemma measurable_preimage_top (hf : Unsigned f) (hix : stmt_ix f) : LebesgueMeasurable (f⁻¹' {⊤}) := by
  rw [ereal_top_singleton_eq, Set.preimage_compl]
  apply LebesgueMeasurable.complement
  rw [Set.preimage_union]
  apply LebesgueMeasurable.union
  · exact measurable_preimage_reals hix
  · rw [unsigned_preimage_bot_empty hf]
    exact LebesgueMeasurable.empty

-- The intersection of an open set with ℝ can be expressed using countable intervals
private lemma open_inter_reals_eq_countable_union (U : Set EReal) (hU : IsOpen U) :
    ∃ S : Set (Set ℝ), S.Countable ∧ (∀ I ∈ S, ∃ a b, I = Set.Ioo a b) ∧
    U ∩ Set.range Real.toEReal = ⋃ I ∈ S, Real.toEReal '' I := by
  let V : Set ℝ := Real.toEReal ⁻¹' U
  have hV_open : IsOpen V := hU.preimage continuous_coe_real_ereal
  let RatIntervals := {I : Set ℝ | ∃ (a b : ℚ), I = Set.Ioo (a : ℝ) b ∧ I ⊆ V}
  have hRI_count : RatIntervals.Countable := by
    have h : RatIntervals ⊆ Set.range (fun p : ℚ × ℚ => Set.Ioo (p.1 : ℝ) p.2) := by
      intro I hI
      obtain ⟨a, b, hab, _⟩ := hI
      exact ⟨(a, b), hab.symm⟩
    exact Set.Countable.mono h (Set.countable_range _)
  have hRI_intervals : ∀ I ∈ RatIntervals, ∃ a b, I = Set.Ioo a b := by
    intro I hI
    obtain ⟨a, b, hab, _⟩ := hI
    exact ⟨a, b, hab⟩
  have hRI_union : V = ⋃ I ∈ RatIntervals, I := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open x hx
      obtain ⟨a, ha_lo, ha_hi⟩ := exists_rat_btwn (by linarith : x - ε / 2 < x)
      obtain ⟨b, hb_lo, hb_hi⟩ := exists_rat_btwn (by linarith : x < x + ε / 2)
      refine ⟨Set.Ioo a b, ?_, ?_⟩
      · refine ⟨a, b, rfl, ?_⟩
        intro y hy
        apply hε_ball
        rw [Metric.mem_ball, Real.dist_eq]
        simp only [Set.mem_Ioo] at hy
        have h1 : y - x < ε / 2 := by linarith [hy.2]
        have h2 : x - y < ε / 2 := by linarith [hy.1]
        rw [abs_lt]
        constructor <;> linarith
      · simp only [Set.mem_Ioo]
        exact ⟨ha_hi, hb_lo⟩
    · intro ⟨I, hI, hxI⟩
      obtain ⟨_, _, _, hI_sub⟩ := hI
      exact hI_sub hxI
  use RatIntervals
  refine ⟨hRI_count, hRI_intervals, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_iUnion, Set.mem_image]
  constructor
  · intro ⟨hy_U, r, hr⟩
    have hr_V : r ∈ V := by
      show Real.toEReal r ∈ U
      rw [hr]; exact hy_U
    rw [hRI_union] at hr_V
    simp only [Set.mem_iUnion] at hr_V
    obtain ⟨I, hI_mem, hr_I⟩ := hr_V
    exact ⟨I, hI_mem, r, hr_I, hr⟩
  · intro ⟨I, hI_mem, r, hr_I, hr⟩
    constructor
    · obtain ⟨_, _, _, hI_sub⟩ := hI_mem
      have : r ∈ V := hI_sub hr_I
      rw [← hr]
      exact this
    · exact ⟨r, hr⟩

private lemma ix_imp_x (hf : Unsigned f) : stmt_ix f → stmt_x f := by
  intro hix U hU
  -- Decompose U = (U ∩ ℝ) ∪ (U ∩ {⊤}) ∪ (U ∩ {⊥})
  have hU_decomp : U = (U ∩ Set.range Real.toEReal) ∪ (U ∩ {⊤}) ∪ (U ∩ {⊥}) := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · intro hx
      induction x using EReal.rec with
      | bot => right; exact ⟨hx, rfl⟩
      | top => left; right; exact ⟨hx, rfl⟩
      | coe r => left; left; exact ⟨hx, r, rfl⟩
    · intro hx
      rcases hx with (⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩ <;> exact hx
  rw [hU_decomp, Set.preimage_union, Set.preimage_union]
  apply LebesgueMeasurable.union
  apply LebesgueMeasurable.union
  -- Part 1: f⁻¹'(U ∩ ℝ) is Lebesgue measurable
  · obtain ⟨S, hS_count, hS_intervals, hS_eq⟩ := open_inter_reals_eq_countable_union U hU
    rw [hS_eq, Set.preimage_iUnion₂]
    -- Use countable encoding of S
    haveI : Countable S := hS_count.to_subtype
    haveI e : Encodable S := Encodable.ofCountable S
    let E' : ℕ → Set (EuclideanSpace' d) := fun n =>
      match @Encodable.decode S e n with
      | some p => f⁻¹' (Real.toEReal '' p.val)
      | none => ∅
    have h_eq' : ⋃ (I : Set ℝ) (_ : I ∈ S), f⁻¹' (Real.toEReal '' I) = ⋃ n, E' n := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_preimage, E']
      constructor
      · intro ⟨I, hI, hx⟩
        use @Encodable.encode S e ⟨I, hI⟩
        simp only [Encodable.encodek]
        exact hx
      · intro ⟨n, hn⟩
        cases hd : @Encodable.decode S e n with
        | none => simp only [hd, Set.mem_empty_iff_false] at hn
        | some p =>
          simp only [hd] at hn
          exact ⟨p.val, p.property, hn⟩
    rw [h_eq']
    apply LebesgueMeasurable.countable_union
    intro n
    simp only [E']
    cases hd : @Encodable.decode S e n with
    | none => exact LebesgueMeasurable.empty
    | some p =>
      simp only
      obtain ⟨a, b, hab⟩ := hS_intervals p.val p.property
      rw [hab]
      exact hix (BoundedInterval.Ioo a b)
  -- Part 2: f⁻¹'(U ∩ {⊤}) is Lebesgue measurable
  · by_cases htop : ⊤ ∈ U
    · have h_eq : U ∩ {⊤} = {⊤} := Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr htop)
      rw [h_eq]
      exact measurable_preimage_top hf hix
    · have h_eq : U ∩ {⊤} = ∅ := Set.inter_singleton_eq_empty.mpr htop
      rw [h_eq, Set.preimage_empty]
      exact LebesgueMeasurable.empty
  -- Part 3: f⁻¹'(U ∩ {⊥}) is Lebesgue measurable (empty for unsigned f)
  · rw [Set.preimage_inter, unsigned_preimage_bot_empty hf, Set.inter_empty]
    exact LebesgueMeasurable.empty

/-! # (x) ⟺ (xi): Complementation -/

private lemma x_iff_xi : stmt_x f ↔ stmt_xi f := by
  constructor
  · intro hx K hK
    have h_eq : f⁻¹' K = (f⁻¹' Kᶜ)ᶜ := by simp
    rw [h_eq]
    exact (hx _ hK.isOpen_compl).complement
  · intro hxi U hU
    have h_eq : f⁻¹' U = (f⁻¹' Uᶜ)ᶜ := by simp
    rw [h_eq]
    exact (hxi _ hU.isClosed_compl).complement

/-! # (x) ⟹ (vii): \{f < λ\} = f⁻¹'({name}`Set.Iio` λ) and {name}`Set.Iio` λ is open -/

private lemma x_imp_vii : stmt_x f → stmt_vii f := by
  intro hx t
  have h_open : IsOpen (Set.Iio t) := isOpen_Iio
  have h_eq : {x | f x < t} = f⁻¹' (Set.Iio t) := rfl
  rw [h_eq]
  exact hx _ h_open

/-! # (v)-(xi) ⟹ (iv): Construction of approximating sequence -/

-- Helper: the norm ball centered at origin is Lebesgue measurable
private lemma normBall_LebesgueMeasurable (r : ℝ) :
    LebesgueMeasurable {x : EuclideanSpace' d | ‖x‖ ≤ r} := by
  have h : {x : EuclideanSpace' d | ‖x‖ ≤ r} = Metric.closedBall 0 r := by
    ext x; simp [Metric.closedBall, dist_zero_right]
  rw [h]
  exact LebesgueMeasurable.closedBall 0 r

end UnsignedMeasurable.TFAE_helpers
