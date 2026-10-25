import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
import Mathlib.Topology.UrysohnsLemma
import Def.Analysis.MeasureTheory.Section_1_3_5.Part2


-- Helper: approximate a scaled box indicator by a continuous compactly supported function
private lemma Box.scaled_indicator_approx_continuous {d:ℕ} (B : Box d) (c : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (g : EuclideanSpace' d → ℝ), Continuous g ∧ CompactlySupported g ∧
      RealAbsolutelyIntegrable g ∧ PreL1.norm (c • B.toSet.indicator' - g) ≤ δ := by
  -- Case 1: c = 0, then g = 0 works
  by_cases hc : c = 0
  · refine ⟨0, continuous_const, ⟨∅, isCompact_empty, fun x _ => rfl⟩,
      RealAbsolutelyIntegrable.zero_fun, ?_⟩
    have : c • B.toSet.indicator' - (0 : EuclideanSpace' d → ℝ) = 0 := by
      ext x; simp [hc]
    rw [this]
    exact PreL1.norm_zero_le (EReal.coe_nonneg.mpr (le_of_lt hδ))
  -- Case 2: c ≠ 0
  · -- B.toSet is elementary, hence Lebesgue measurable with finite measure
    have hB_elem : IsElementary B.toSet := IsElementary.box B
    have hB_meas : LebesgueMeasurable B.toSet :=
      Jordan_measurable.lebesgue (IsElementary.jordanMeasurable hB_elem)
    have hB_fin : Lebesgue_measure B.toSet < ⊤ := by
      unfold Lebesgue_measure
      rw [Lebesgue_outer_measure.elementary B.toSet hB_elem]
      exact EReal.coe_lt_top _
    -- Choose ε₀ = δ / (2 * |c|) > 0
    have hc_abs_pos : 0 < |c| := abs_pos.mpr hc
    set ε₀ : ℝ := δ / (2 * |c|) with hε₀_def
    have hε₀ : 0 < ε₀ := div_pos hδ (mul_pos two_pos hc_abs_pos)
    -- Get compact K ⊆ B.toSet with measure(B.toSet \ K) ≤ ε₀
    have h_tfae_03 := (LebesgueMeasurable.finite_TFAE B.toSet).out 1 4
    obtain ⟨K, hK_compact, hK_sub, hK_bound⟩ :=
      h_tfae_03.mp ⟨hB_meas, hB_fin⟩ (↑ε₀) (EReal.coe_pos.mpr hε₀)
    -- Get open U ⊇ B.toSet with measure(U \ B.toSet) ≤ ε₀ and finite measure
    have h_tfae_01 := (LebesgueMeasurable.finite_TFAE B.toSet).out 1 2
    obtain ⟨U, hU_open, hB_sub_U, hU_fin, hU_diff_bound⟩ :=
      h_tfae_01.mp ⟨hB_meas, hB_fin⟩ (↑ε₀) (EReal.coe_pos.mpr hε₀)
    -- K ⊆ U (since K ⊆ B.toSet ⊆ U)
    have hKU : K ⊆ U := hK_sub.trans hB_sub_U
    -- K and Uᶜ are disjoint
    have hKU_disj : Disjoint K Uᶜ :=
      Set.disjoint_compl_right_iff_subset.mpr hKU
    -- Apply Urysohn: get continuous φ with HasCompactSupport, φ=1 on K, φ=0 outside U
    obtain ⟨φ, hφ_one, hφ_zero, hφ_cs, hφ_range⟩ :=
      exists_continuous_one_zero_of_isCompact hK_compact hU_open.isClosed_compl hKU_disj
    -- Define g = c • φ
    set g : EuclideanSpace' d → ℝ := fun x => c * φ x with hg_def
    -- Set up notation for the difference
    set diff : EuclideanSpace' d → ℝ := c • B.toSet.indicator' - g with hdiff_def
    -- Key properties of φ
    have hφ_zero' : ∀ x, x ∉ U → φ x = 0 := by
      intro x hxU
      have := hφ_zero (show x ∈ Uᶜ from hxU)
      simp at this; exact this
    -- Pointwise bound: |diff(x)| ≤ |c| and diff = 0 outside U
    have hdiff_bound : ∀ x, ‖diff x‖ ≤ |c| := by
      intro x
      simp only [diff, hg_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hφ_bdd := hφ_range x
      rw [show c * B.toSet.indicator' x - c * φ x = c * (B.toSet.indicator' x - φ x) by ring]
      rw [norm_mul, Real.norm_eq_abs]
      apply mul_le_of_le_one_right (abs_nonneg c)
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · by_cases hxB : x ∈ B.toSet
        · rw [Set.indicator'_of_mem hxB]; linarith [hφ_bdd.2]
        · rw [Set.indicator'_of_notMem hxB]; linarith [hφ_bdd.2]
      · by_cases hxB : x ∈ B.toSet
        · rw [Set.indicator'_of_mem hxB]; linarith [hφ_bdd.1]
        · rw [Set.indicator'_of_notMem hxB]; linarith [hφ_bdd.1]
    have hdiff_support : ∀ x, x ∉ U → diff x = 0 := by
      intro x hxU
      simp only [diff, hg_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [Set.indicator'_of_notMem (fun h => hxU (hB_sub_U h)), mul_zero,
        hφ_zero' x hxU, mul_zero, sub_self]
    -- Measurability
    have hg_meas : RealMeasurable g :=
      (continuous_const.mul φ.continuous).RealMeasurable
    have hcB_ai : RealAbsolutelyIntegrable (c • B.toSet.indicator') :=
      RealAbsolutelyIntegrable.smul_indicator hB_meas c (fun _ => hB_fin)
    have hdiff_meas : RealMeasurable diff := RealMeasurable.sub hcB_ai.1 hg_meas
    -- Measurability of sets involved
    have hBK_meas : LebesgueMeasurable (B.toSet \ K) :=
      hB_meas.inter (hK_compact.isClosed.measurable).complement
    have hUB_meas : LebesgueMeasurable (U \ B.toSet) :=
      (IsOpen.measurable hU_open).inter hB_meas.complement
    -- Key pointwise bound: |diff(x)| ≤ |c| * (1_{B\K}(x) + 1_{U\B}(x))
    -- Also: simpler bound |diff(x)| ≤ |c| * 1_U(x) for AI proof
    have h_pw_U : ∀ x, EReal.abs_fun diff x ≤
        ((Real.toEReal |c|) • (Real.toEReal ∘ U.indicator')) x := by
      intro x
      simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, Function.comp]
      by_cases hxU : x ∈ U
      · rw [Set.indicator'_of_mem hxU]
        have : Real.toEReal 1 = (1 : EReal) := rfl
        rw [this, mul_one]
        exact EReal.coe_le_coe_iff.mpr (hdiff_bound x)
      · rw [hdiff_support x hxU, norm_zero, Set.indicator'_of_notMem hxU]
        have : Real.toEReal 0 = (0 : EReal) := rfl
        rw [this, mul_zero]
    -- Tighter pointwise bound (for the norm bound)
    have h_pw_tight : ∀ x, EReal.abs_fun diff x ≤
        ((Real.toEReal |c|) • ((Real.toEReal ∘ (B.toSet \ K).indicator') +
                                (Real.toEReal ∘ (U \ B.toSet).indicator'))) x := by
      intro x
      simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, Function.comp, Pi.add_apply]
      by_cases hxK : x ∈ K
      · -- On K: diff = 0
        have hdx : diff x = 0 := by
          simp only [diff, hg_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          have h1 := hφ_one hxK; simp only [Pi.one_apply] at h1
          rw [Set.indicator'_of_mem (hK_sub hxK), mul_one, h1, mul_one, sub_self]
        rw [hdx, norm_zero]
        apply mul_nonneg (EReal.coe_nonneg.mpr (abs_nonneg c))

        apply add_nonneg <;> exact EReal.coe_nonneg.mpr ((Set.indicator_nonneg (fun _ _ => zero_le_one) x))
      · by_cases hxB : x ∈ B.toSet
        · -- On B \ K: |diff| ≤ |c|, bound by |c| * 1
          rw [Set.indicator'_of_mem (show x ∈ B.toSet \ K from ⟨hxB, hxK⟩),
            Set.indicator'_of_notMem (show x ∉ U \ B.toSet from fun h => h.2 hxB)]
          have h0 : Real.toEReal 0 = (0 : EReal) := rfl
          have h1 : Real.toEReal 1 = (1 : EReal) := rfl
          rw [h1, h0, add_zero, mul_one]
          exact EReal.coe_le_coe_iff.mpr (hdiff_bound x)
        · by_cases hxU : x ∈ U
          · -- On U \ B: |diff| ≤ |c|, bound by |c| * 1
            rw [Set.indicator'_of_notMem (show x ∉ B.toSet \ K from fun h => hxB h.1),
              Set.indicator'_of_mem (show x ∈ U \ B.toSet from ⟨hxU, hxB⟩)]
            have h0 : Real.toEReal 0 = (0 : EReal) := rfl
            have h1 : Real.toEReal 1 = (1 : EReal) := rfl
            rw [h0, h1, zero_add, mul_one]
            exact EReal.coe_le_coe_iff.mpr (hdiff_bound x)
          · -- Outside U: diff = 0
            rw [hdiff_support x hxU, norm_zero]
            apply mul_nonneg (EReal.coe_nonneg.mpr (abs_nonneg c))
            apply add_nonneg <;> exact EReal.coe_nonneg.mpr ((Set.indicator_nonneg (fun _ _ => zero_le_one) x))
    -- Derive AI for diff (using the U bound)
    have hU_meas : LebesgueMeasurable U := IsOpen.measurable hU_open
    have hU_simple := UnsignedSimpleFunction.indicator hU_meas
    have hc_nn : (Real.toEReal |c|) ≥ 0 := by exact_mod_cast abs_nonneg c
    have hdiff_abs_meas : UnsignedMeasurable (EReal.abs_fun diff) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨g, hg_simple, hg_conv⟩ := hdiff_meas
        exact ⟨fun n => EReal.abs_fun (g n), fun n => (hg_simple n).abs, fun x => by
          simp only [EReal.abs_fun]
          exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)⟩
    have hdiff_ai : RealAbsolutelyIntegrable diff := by
      constructor
      · exact hdiff_meas
      · have hbound_simple := hU_simple.smul hc_nn
        have hbound_meas := UnsignedSimpleFunction.unsignedMeasurable hbound_simple
        have h_mono := LowerUnsignedLebesgueIntegral.mono
          hdiff_abs_meas hbound_meas
          (AlmostAlways.ofAlways h_pw_U)
        have h_integ : LowerUnsignedLebesgueIntegral
            ((Real.toEReal |c|) • (Real.toEReal ∘ U.indicator')) =
            (Real.toEReal |c|) * Lebesgue_measure U := by
          rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral hbound_simple,
            UnsignedSimpleFunction.integral_smul hU_simple hc_nn,
            UnsignedSimpleFunction.integral_indicator hU_meas]
        rw [UnsignedLebesgueIntegral]
        calc LowerUnsignedLebesgueIntegral (EReal.abs_fun diff)
            ≤ LowerUnsignedLebesgueIntegral
                ((Real.toEReal |c|) • (Real.toEReal ∘ U.indicator')) := h_mono
          _ = (Real.toEReal |c|) * Lebesgue_measure U := h_integ
          _ < ⊤ := by
              apply Ne.lt_top
              exact (EReal.mul_ne_top (↑|c|) (Lebesgue_measure U)).mpr
                ⟨Or.inl (EReal.coe_ne_bot _),
                 Or.inl (le_of_lt (EReal.coe_pos.mpr hc_abs_pos)),
                 Or.inl (EReal.coe_ne_top _),
                 Or.inr (ne_of_lt hU_fin)⟩
    -- g = (c • B.toSet.indicator') - diff, so g is AI
    have hg_ai : RealAbsolutelyIntegrable g := by
      have : g = c • B.toSet.indicator' - diff := by
        ext x; simp [diff, hg_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [this]
      exact hcB_ai.sub hdiff_ai
    refine ⟨g, ?_, ?_, hg_ai, ?_⟩
    -- g is continuous
    · exact continuous_const.mul φ.continuous
    -- g is compactly supported
    · refine ⟨tsupport φ, hφ_cs, fun x hx => ?_⟩
      simp only [hg_def]
      have : φ x = 0 := by
        by_contra h
        exact hx (subset_tsupport φ (Function.mem_support.mpr h))
      rw [this, mul_zero]
    -- PreL1.norm bound: PreL1.norm diff ≤ δ
    · -- Use the tight pointwise bound
      have hBK_simple := UnsignedSimpleFunction.indicator hBK_meas
      have hUB_simple := UnsignedSimpleFunction.indicator hUB_meas
      have hsum_simple : UnsignedSimpleFunction
          ((Real.toEReal ∘ (B.toSet \ K).indicator') +
           (Real.toEReal ∘ (U \ B.toSet).indicator')) :=
        UnsignedSimpleFunction.add hBK_simple hUB_simple
      have hbound_simple := hsum_simple.smul hc_nn
      have hbound_meas2 := UnsignedSimpleFunction.unsignedMeasurable hbound_simple
      have h_mono := LowerUnsignedLebesgueIntegral.mono
        hdiff_abs_meas hbound_meas2
        (AlmostAlways.ofAlways h_pw_tight)
      have h_integ_bound : LowerUnsignedLebesgueIntegral
          ((Real.toEReal |c|) • ((Real.toEReal ∘ (B.toSet \ K).indicator') +
                                  (Real.toEReal ∘ (U \ B.toSet).indicator'))) =
          (Real.toEReal |c|) * (Lebesgue_measure (B.toSet \ K) +
                                 Lebesgue_measure (U \ B.toSet)) := by
        rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral hbound_simple,
          UnsignedSimpleFunction.integral_smul hsum_simple hc_nn]
        congr 1
        rw [← LowerUnsignedLebesgueIntegral.eq_simpleIntegral hsum_simple,
          LowerUnsignedLebesgueIntegral.add
          (UnsignedSimpleFunction.unsignedMeasurable hBK_simple)
          (UnsignedSimpleFunction.unsignedMeasurable hUB_simple)
          (UnsignedSimpleFunction.unsignedMeasurable hsum_simple),
          LowerUnsignedLebesgueIntegral.eq_simpleIntegral hBK_simple,
          LowerUnsignedLebesgueIntegral.eq_simpleIntegral hUB_simple,
          UnsignedSimpleFunction.integral_indicator hBK_meas,
          UnsignedSimpleFunction.integral_indicator hUB_meas]
      unfold PreL1.norm UnsignedLebesgueIntegral
      calc LowerUnsignedLebesgueIntegral (EReal.abs_fun diff)
          ≤ LowerUnsignedLebesgueIntegral
              ((Real.toEReal |c|) • ((Real.toEReal ∘ (B.toSet \ K).indicator') +
                                      (Real.toEReal ∘ (U \ B.toSet).indicator'))) := h_mono
        _ = (Real.toEReal |c|) * (Lebesgue_measure (B.toSet \ K) +
                                   Lebesgue_measure (U \ B.toSet)) := h_integ_bound
        _ ≤ (Real.toEReal |c|) * (↑ε₀ + ↑ε₀) := by
            apply mul_le_mul_of_nonneg_left _ hc_nn.le
            unfold Lebesgue_measure
            exact add_le_add hK_bound hU_diff_bound
        _ = ↑δ := by
            rw [← EReal.coe_add, ← EReal.coe_mul]
            congr 1
            rw [hε₀_def]
            field_simp
            ring

-- Helper: a step function can be approximated by a continuous compactly supported function
private lemma RealStepFunction.approx_by_continuous_compact_aux {d:ℕ}
    {h : EuclideanSpace' d → ℝ} (hh : RealStepFunction h) (_hh_ai : RealAbsolutelyIntegrable h)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (g : EuclideanSpace' d → ℝ), Continuous g ∧ CompactlySupported g ∧
      RealAbsolutelyIntegrable g ∧ PreL1.norm (h - g) ≤ δ := by
  obtain ⟨S, c, hh_eq⟩ := hh
  -- Handle empty finset
  by_cases hS : S = ∅
  · have hh_zero : h = 0 := by
      subst hS; rw [hh_eq]; simp [Finset.univ_eq_empty]
    refine ⟨0, continuous_const, ⟨∅, isCompact_empty, fun x _ => rfl⟩,
      RealAbsolutelyIntegrable.zero_fun, ?_⟩
    rw [hh_zero, sub_zero]
    exact PreL1.norm_zero_le (EReal.coe_nonneg.mpr (le_of_lt hδ))
  -- S is nonempty
  · have hS_nonempty : S.Nonempty := Finset.nonempty_of_ne_empty hS
    have hS_card_pos : 0 < S.card := Finset.Nonempty.card_pos hS_nonempty
    have hS_card_pos_real : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS_card_pos
    -- Budget per box
    have hδ_per : 0 < δ / S.card := div_pos hδ hS_card_pos_real
    -- For each box B ∈ S, approximate c B • B.val.toSet.indicator' by continuous g_B
    have h_approx : ∀ B : S, ∃ (g_B : EuclideanSpace' d → ℝ),
        Continuous g_B ∧ CompactlySupported g_B ∧
        RealAbsolutelyIntegrable g_B ∧
        PreL1.norm (c B • B.val.toSet.indicator' - g_B) ≤ δ / S.card :=
      fun B => Box.scaled_indicator_approx_continuous B.val (c B) (δ / S.card) hδ_per
    choose g_B hg_cont hg_cs hg_ai hg_norm using h_approx
    -- Define g = ∑ B ∈ S, g_B
    set g : EuclideanSpace' d → ℝ := fun x => ∑ B : S, g_B B x with hg_def
    -- h - g = ∑ B ∈ S, (c B • B.val.toSet.indicator' - g_B B)
    have hfg_eq : h - g = fun x => ∑ B : S, (c B • B.val.toSet.indicator' - g_B B) x := by
      ext x
      simp only [Pi.sub_apply, hg_def, hh_eq, Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_sub_distrib]
    -- Each term is AI
    have hterm_ai : ∀ B : S,
        RealAbsolutelyIntegrable (c B • B.val.toSet.indicator' - g_B B) :=
      fun B => by
        have hB_meas : LebesgueMeasurable B.val.toSet :=
          Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (IsElementary.box B.val))
        have hB_fin : Lebesgue_measure B.val.toSet < ⊤ := by
          unfold Lebesgue_measure
          rw [Lebesgue_outer_measure.elementary B.val.toSet (IsElementary.box B.val)]
          exact EReal.coe_lt_top _
        exact (RealAbsolutelyIntegrable.smul_indicator hB_meas (c B) (fun _ => hB_fin)).sub
          (hg_ai B)
    refine ⟨g, ?_, ?_, ?_, ?_⟩
    -- g is continuous
    · show Continuous g
      apply continuous_finset_sum
      intro B _
      exact hg_cont B
    -- g is compactly supported
    · obtain ⟨B₀, hB₀⟩ := hS_nonempty
      -- Each g_B has compact support K_B
      choose K hK_compact hK_support using fun B => (hg_cs B)
      refine ⟨⋃ B : S, K B, ?_, ?_⟩
      · exact isCompact_iUnion (fun B => (hK_compact B))
      · intro x hx
        rw [Set.mem_iUnion] at hx
        push_neg at hx
        simp only [hg_def]
        exact Finset.sum_eq_zero (fun B _ => hK_support B x (hx B))
    -- g is AI (sum of AI functions)
    · show RealAbsolutelyIntegrable g
      have hg_eq_sum : g = ∑ B : S, g_B B := by
        ext x; simp [hg_def]
      rw [hg_eq_sum]
      exact Finset.sum_induction _ RealAbsolutelyIntegrable
        (fun f g hf hg => hf.add hg) RealAbsolutelyIntegrable.zero_fun
        (fun B _ => hg_ai B)
    -- PreL1.norm (h - g) ≤ δ
    · -- Set up difference terms
      set diff_term : S → (EuclideanSpace' d → ℝ) :=
        fun B => c B • B.val.toSet.indicator' - g_B B with hdiff_term_def
      -- h - g = ∑ diff_term
      have hfg_eq' : h - g = ∑ B : S, diff_term B := by
        ext x
        simp only [Pi.sub_apply, hh_eq, hg_def, hdiff_term_def, Finset.sum_apply,
          Pi.smul_apply, Pi.sub_apply]
        rw [Finset.sum_sub_distrib]
      -- Prove by finset induction: AI of partial sum and norm bound
      suffices h_bound : ∀ (T : Finset S),
          RealAbsolutelyIntegrable (∑ B ∈ T, diff_term B) ∧
          PreL1.norm (∑ B ∈ T, diff_term B) ≤
          ∑ B ∈ T, PreL1.norm (diff_term B) by
        rw [hfg_eq']
        have h1 := (h_bound Finset.univ).2
        calc PreL1.norm (∑ B : S, diff_term B)
            ≤ ∑ B : S, PreL1.norm (diff_term B) := h1
          _ ≤ ∑ _B : S, (↑(δ / ↑S.card) : EReal) :=
              Finset.sum_le_sum (fun B _ => hg_norm B)
          _ = ↑δ := by
              rw [← EReal.coe_finset_sum (fun _ _ => le_of_lt hδ_per)]
              congr 1
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
                nsmul_eq_mul, mul_div_cancel₀ δ
                  (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hS_card_pos))]
      -- Prove the suffices by induction
      intro T
      induction T using Finset.induction with
      | empty =>
        simp only [Finset.sum_empty]
        exact ⟨RealAbsolutelyIntegrable.zero_fun, PreL1.norm_zero_le le_rfl⟩
      | @insert a T' haT ih =>
        rw [Finset.sum_insert haT, Finset.sum_insert haT]
        set f_a := diff_term a
        set sum_T := ∑ B ∈ T', diff_term B
        have hfa_ai : RealAbsolutelyIntegrable f_a := hterm_ai a
        have hsum_ai : RealAbsolutelyIntegrable sum_T := ih.1
        constructor
        · exact hfa_ai.add hsum_ai
        · -- Triangle inequality
          have h_eq1 : (f_a + sum_T) - sum_T = f_a := by
            ext x; simp [f_a, sum_T, Pi.add_apply, Pi.sub_apply]
          have h_eq2 : sum_T - 0 = sum_T := by ext x; simp
          have h_eq3 : (f_a + sum_T) - 0 = f_a + sum_T := by ext x; simp
          have hfg_ai' : RealAbsolutelyIntegrable ((f_a + sum_T) - sum_T) := by
            rw [h_eq1]; exact hfa_ai
          have hgh_ai' : RealAbsolutelyIntegrable (sum_T - 0) := by
            rw [h_eq2]; exact hsum_ai
          have hfg : PreL1.norm ((f_a + sum_T) - sum_T) ≤ PreL1.norm f_a := by rw [h_eq1]
          have hgh : PreL1.norm (sum_T - 0) ≤ PreL1.norm sum_T := by rw [h_eq2]
          calc PreL1.norm (f_a + sum_T)
              = PreL1.norm ((f_a + sum_T) - 0) := by congr 1; exact h_eq3.symm
            _ ≤ PreL1.norm f_a + PreL1.norm sum_T :=
                PreL1.norm_sub_le_add hfg_ai' hgh_ai' hfg hgh
            _ ≤ PreL1.norm f_a +
                ∑ B ∈ T', PreL1.norm (diff_term B) :=
                add_le_add le_rfl ih.2

/-- Theorem 1.3.20(iii) Approximation of $L^1$ functions by continuous compactly supported functions -/
theorem RealAbsolutelyIntegrable.approx_by_continuous_compact {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → ℝ), Continuous g ∧ CompactlySupported g ∧
        PreL1.norm (f - g) ≤ ε := by
  -- Step 1: approximate f by step function h
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨h, hh_step, hh_ai, hh_norm⟩ := hf.approx_by_step (ε / 2) hε2
  -- Step 4: approximate step function h by continuous compactly supported g
  obtain ⟨g, hg_cont, hg_cs, hg_ai, hg_norm⟩ :=
    RealStepFunction.approx_by_continuous_compact_aux hh_step hh_ai (ε / 2) hε2
  -- Step 5: combine via triangle inequality
  refine ⟨g, hg_cont, hg_cs, ?_⟩
  have h_combined := PreL1.norm_sub_le_add (hf.sub hh_ai) (hh_ai.sub hg_ai) hh_norm hg_norm
  calc PreL1.norm (f - g) ≤ ↑(ε / 2) + ↑(ε / 2) := h_combined
    _ = (ε : EReal) := by rw [← EReal.coe_add]; congr 1; linarith

theorem ComplexAbsolutelyIntegrable.approx_by_continuous_compact {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), Continuous g ∧ CompactlySupported g ∧
    PreL1.norm (f - g) ≤ ε := by
  -- Approximate real and imaginary parts within ε/2
  -- Use internal aux helpers to also get RealAbsolutelyIntegrable
  have hε2 : 0 < ε / 2 := half_pos hε
  have hε4 : 0 < ε / 2 / 2 := half_pos hε2
  -- Real part: step function approximation then continuous approximation
  obtain ⟨h_re, hh_re_step, hh_re_ai, hh_re_norm⟩ :=
    (ComplexAbsolutelyIntegrable.re f hf).approx_by_step (ε / 2 / 2) hε4
  obtain ⟨g_re, hg_re_cont, hg_re_cs, hg_re_ai, hg_re_norm'⟩ :=
    RealStepFunction.approx_by_continuous_compact_aux hh_re_step hh_re_ai (ε / 2 / 2) hε4
  have hg_re_norm : PreL1.norm (Complex.re_fun f - g_re) ≤ ↑(ε / 2) := by
    have := PreL1.norm_sub_le_add ((ComplexAbsolutelyIntegrable.re f hf).sub hh_re_ai)
      (hh_re_ai.sub hg_re_ai) hh_re_norm hg_re_norm'
    calc PreL1.norm (Complex.re_fun f - g_re)
        ≤ ↑(ε / 2 / 2) + ↑(ε / 2 / 2) := this
      _ = ↑(ε / 2) := by rw [← EReal.coe_add]; congr 1; linarith
  -- Imaginary part: step function approximation then continuous approximation
  obtain ⟨h_im, hh_im_step, hh_im_ai, hh_im_norm⟩ :=
    (ComplexAbsolutelyIntegrable.im f hf).approx_by_step (ε / 2 / 2) hε4
  obtain ⟨g_im, hg_im_cont, hg_im_cs, hg_im_ai, hg_im_norm'⟩ :=
    RealStepFunction.approx_by_continuous_compact_aux hh_im_step hh_im_ai (ε / 2 / 2) hε4
  have hg_im_norm : PreL1.norm (Complex.im_fun f - g_im) ≤ ↑(ε / 2) := by
    have := PreL1.norm_sub_le_add ((ComplexAbsolutelyIntegrable.im f hf).sub hh_im_ai)
      (hh_im_ai.sub hg_im_ai) hh_im_norm hg_im_norm'
    calc PreL1.norm (Complex.im_fun f - g_im)
        ≤ ↑(ε / 2 / 2) + ↑(ε / 2 / 2) := this
      _ = ↑(ε / 2) := by rw [← EReal.coe_add]; congr 1; linarith
  -- Construct complex approximation g = ↑g_re + I • ↑g_im
  set g : EuclideanSpace' d → ℂ :=
    Real.complex_fun g_re + Complex.I • Real.complex_fun g_im with hg_def
  have hg_re_eq : Complex.re_fun g = g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hg_im_eq : Complex.im_fun g = g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  -- g is continuous
  have hg_cont : Continuous g := by
    apply Continuous.add
    · exact Complex.continuous_ofReal.comp hg_re_cont
    · exact continuous_const.mul (Complex.continuous_ofReal.comp hg_im_cont)
  -- g is compactly supported
  have hg_cs : CompactlySupported g := by
    obtain ⟨K_re, hK_re_compact, hK_re_supp⟩ := hg_re_cs
    obtain ⟨K_im, hK_im_compact, hK_im_supp⟩ := hg_im_cs
    refine ⟨K_re ∪ K_im, hK_re_compact.union hK_im_compact, fun x hx => ?_⟩
    rw [Set.mem_union] at hx; push_neg at hx
    simp only [hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.complex_fun]
    rw [hK_re_supp x hx.1, hK_im_supp x hx.2]
    simp
  -- g is absolutely integrable
  have hg_ai : ComplexAbsolutelyIntegrable g := by
    apply (ComplexAbsolutelyIntegrable.iff g).mpr
    exact ⟨hg_re_eq ▸ hg_re_ai, hg_im_eq ▸ hg_im_ai⟩
  refine ⟨g, hg_cont, hg_cs, ?_⟩
  -- Norm bound: PreL1.norm (f - g) ≤ ε
  show UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤ (ε : EReal)
  have hfg_re : Complex.re_fun (f - g) = Complex.re_fun f - g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hfg_im : Complex.im_fun (f - g) = Complex.im_fun f - g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  have h_bound : ∀ x, EReal.abs_fun (f - g) x ≤
      (EReal.abs_fun (Complex.re_fun (f - g)) + EReal.abs_fun (Complex.im_fun (f - g))) x :=
    fun x => by
      simp only [EReal.abs_fun, Complex.re_fun, Complex.im_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by
        calc ‖(f - g) x‖ ≤ |((f - g) x).re| + |((f - g) x).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ = ‖((f - g) x).re‖ + ‖((f - g) x).im‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs])
  have hfg_ai := hf.sub hg_ai
  have hfg_re_ai := ComplexAbsolutelyIntegrable.re (f - g) hfg_ai
  have hfg_im_ai := ComplexAbsolutelyIntegrable.im (f - g) hfg_ai
  have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
                                EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.mono hfg_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1) (AlmostAlways.ofAlways h_bound)
  have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
      EReal.abs_fun (Complex.im_fun (f - g))) =
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g))) +
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.add hfg_re_ai.abs.1 hfg_im_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1)
  rw [h_add] at h_mono
  rw [show EReal.abs_fun (Complex.re_fun (f - g)) =
        EReal.abs_fun (Complex.re_fun f - g_re) from by rw [hfg_re],
      show EReal.abs_fun (Complex.im_fun (f - g)) =
        EReal.abs_fun (Complex.im_fun f - g_im) from by rw [hfg_im]] at h_mono
  calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g))
      ≤ UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f - g_re)) +
        UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f - g_im)) := h_mono
    _ ≤ (↑(ε / 2) : EReal) + (↑(ε / 2) : EReal) := add_le_add hg_re_norm hg_im_norm
    _ = (ε : EReal) := by rw [← EReal.coe_add]; congr 1; linarith

