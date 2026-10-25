import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Def.Analysis.MeasureTheory.Section_1_3_2.Part8
set_option doc.verso.suggestions false


namespace Remark_1_3_10

lemma f_lifted_unsigned : Unsigned f_lifted := by
  intro x
  simp only [f_lifted, ge_iff_le]
  rw [EReal.coe_nonneg]
  exact le_max_left 0 _

lemma f_lifted_le_one (x : EuclideanSpace' 1) : f_lifted x ≤ 1 := by
  simp only [f_lifted]
  have hg := binaryToTernary_props.bounded (EuclideanSpace'.equiv_Real x)
  have h_max_le : max 0 (binaryToTernary (EuclideanSpace'.equiv_Real x)) ≤ 1 :=
    max_le (by norm_num) hg
  exact EReal.coe_le_coe_iff.mpr h_max_le

lemma f_lifted_zero_outside (x : EuclideanSpace' 1) (hx : EuclideanSpace'.equiv_Real x ∉ Set.Icc 0 1) :
    f_lifted x = 0 := by
  simp only [f_lifted]
  have hg := binaryToTernary_props.zero_outside (EuclideanSpace'.equiv_Real x) hx
  rw [hg]
  simp

lemma f_lifted_zero_at_zero (x : EuclideanSpace' 1) (hx : EuclideanSpace'.equiv_Real x = 0) :
    f_lifted x = 0 := by
  simp only [f_lifted]
  have hg := binaryToTernary_props.zero_at_zero
  rw [hx, hg]
  simp

lemma f_zero_set_in_interval_countable :
    (Set.Icc (0:ℝ) 1 ∩ {x | binaryToTernary x = 0}).Countable :=
  binaryToTernary_props.zero_set_countable

lemma f_lifted_zero_set_measurable : LebesgueMeasurable {x : EuclideanSpace' 1 | f_lifted x = 0} := by
  have h_decomp : {x : EuclideanSpace' 1 | f_lifted x = 0} =
      (Real.equiv_EuclideanSpace' '' (Set.Icc 0 1)ᶜ) ∪
      (Real.equiv_EuclideanSpace' '' (Set.Icc 0 1 ∩ {x | binaryToTernary x = 0})) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
    constructor
    · intro hfx
      simp only [f_lifted] at hfx
      have hmax : max 0 (binaryToTernary (EuclideanSpace'.equiv_Real x)) = 0 := by
        rw [EReal.coe_eq_zero] at hfx
        exact hfx
      have hbinary : binaryToTernary (EuclideanSpace'.equiv_Real x) ≤ 0 := by
        have := le_max_right 0 (binaryToTernary (EuclideanSpace'.equiv_Real x))
        rw [hmax] at this
        exact this
      have hbinary_nonneg := binaryToTernary_props.nonneg (EuclideanSpace'.equiv_Real x)
      have hbinary_eq : binaryToTernary (EuclideanSpace'.equiv_Real x) = 0 :=
        le_antisymm hbinary hbinary_nonneg
      by_cases h_in : EuclideanSpace'.equiv_Real x ∈ Set.Icc 0 1
      · right
        use EuclideanSpace'.equiv_Real x
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · exact ⟨h_in, hbinary_eq⟩
        · exact EuclideanSpace'.equiv_Real.symm_apply_apply x
      · left
        use EuclideanSpace'.equiv_Real x
        simp only [Set.mem_compl_iff]
        exact ⟨h_in, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
    · intro h
      rcases h with ⟨r, hr, hrx⟩ | ⟨r, ⟨hr_in, hr_zero⟩, hrx⟩
      · simp only [f_lifted]
        have hx_eq : EuclideanSpace'.equiv_Real x = r := by
          rw [← hrx]; exact EuclideanSpace'.equiv_Real.apply_symm_apply r
        rw [hx_eq, binaryToTernary_props.zero_outside r hr]; simp
      · simp only [f_lifted]
        have hx_eq : EuclideanSpace'.equiv_Real x = r := by
          rw [← hrx]; exact EuclideanSpace'.equiv_Real.apply_symm_apply r
        rw [hx_eq, hr_zero]; simp
  rw [h_decomp]
  apply LebesgueMeasurable.union
  · apply IsOpen.measurable
    have h_open : IsOpen (Set.Icc (0:ℝ) 1)ᶜ := isOpen_compl_iff.mpr isClosed_Icc
    have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
      show Continuous (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
      exact continuous_induced_rng.mpr (continuous_pi (fun _ => continuous_id))
    have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
      exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) ⟨0, by decide⟩
    let e : ℝ ≃ₜ EuclideanSpace' 1 :=
      { toEquiv := Real.equiv_EuclideanSpace'
        continuous_toFun := hf_cont
        continuous_invFun := hg_cont }
    exact e.isOpenMap (Set.Icc 0 1)ᶜ h_open
  · apply IsNull.measurable
    have h_countable : (Real.equiv_EuclideanSpace' '' (Set.Icc 0 1 ∩ {x | binaryToTernary x = 0})).Countable := by
      apply Set.Countable.image; exact f_zero_set_in_interval_countable
    exact Countable.Lebesgue_measure Nat.one_pos h_countable

/-- Sublevel sets of {name}`f_lifted` are measurable (key lemma for `f_lifted_measurable`). -/
lemma sublevel_set_measurable (t : EReal) (ht_pos : 0 < t) (ht_lt_one : t < 1) :
    LebesgueMeasurable {x : EuclideanSpace' 1 | f_lifted x ≤ t} := by
  have h_outside_zero : ∀ x : EuclideanSpace' 1, EuclideanSpace'.equiv_Real x ∉ Set.Icc 0 1 →
      f_lifted x ≤ t := fun x hx => by rw [f_lifted_zero_outside x hx]; exact le_of_lt ht_pos
  have h_decomp : {x : EuclideanSpace' 1 | f_lifted x ≤ t} =
      (Real.equiv_EuclideanSpace' '' Set.Iio 0) ∪
      (Real.equiv_EuclideanSpace' '' Set.Ioi 1) ∪
      {x : EuclideanSpace' 1 | EuclideanSpace'.equiv_Real x ∈ Set.Icc 0 1 ∧ f_lifted x ≤ t} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
    constructor
    · intro hfx
      by_cases h_neg : EuclideanSpace'.equiv_Real x < 0
      · left; left
        use EuclideanSpace'.equiv_Real x
        exact ⟨h_neg, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
      · by_cases h_big : EuclideanSpace'.equiv_Real x > 1
        · left; right
          use EuclideanSpace'.equiv_Real x
          exact ⟨h_big, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
        · right
          push_neg at h_neg h_big
          exact ⟨⟨h_neg, h_big⟩, hfx⟩
    · intro h
      rcases h with (⟨r, hr, hrx⟩ | ⟨r, hr, hrx⟩) | ⟨h_in, hfx⟩
      · apply h_outside_zero
        rw [← hrx, EuclideanSpace'.equiv_Real.apply_symm_apply]
        simp only [Set.mem_Icc, not_and, not_le, Set.mem_Iio] at hr ⊢
        intro; linarith
      · apply h_outside_zero
        rw [← hrx, EuclideanSpace'.equiv_Real.apply_symm_apply]
        simp only [Set.mem_Icc, not_and, not_le, Set.mem_Ioi] at hr ⊢
        intro; linarith
      · exact hfx
  rw [h_decomp]
  apply LebesgueMeasurable.union
  apply LebesgueMeasurable.union
  · apply IsOpen.measurable
    have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
      show Continuous (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
      exact continuous_induced_rng.mpr (continuous_pi (fun _ => continuous_id))
    have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
      exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) ⟨0, by decide⟩
    let e : ℝ ≃ₜ EuclideanSpace' 1 :=
      { toEquiv := Real.equiv_EuclideanSpace'
        continuous_toFun := hf_cont
        continuous_invFun := hg_cont }
    exact e.isOpenMap (Set.Iio 0) isOpen_Iio
  · apply IsOpen.measurable
    have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
      show Continuous (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
      exact continuous_induced_rng.mpr (continuous_pi (fun _ => continuous_id))
    have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
      exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) ⟨0, by decide⟩
    let e : ℝ ≃ₜ EuclideanSpace' 1 :=
      { toEquiv := Real.equiv_EuclideanSpace'
        continuous_toFun := hf_cont
        continuous_invFun := hg_cont }
    exact e.isOpenMap (Set.Ioi 1) isOpen_Ioi
  · -- Monotonicity case: {x ∈ [0,1] | f_lifted x ≤ t} is a convex set, hence measurable
    have ht_ne_top : t ≠ ⊤ := ne_of_lt (lt_of_lt_of_le ht_lt_one le_top)
    have ht_ne_bot : t ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le ht_pos)
    let t' := t.toReal
    have ht_eq : t = (t' : EReal) := (EReal.coe_toReal ht_ne_top ht_ne_bot).symm
    rw [ht_eq]
    have ht'_pos : 0 < t' := by
      have h : (0:EReal) < t := ht_pos
      rw [ht_eq, EReal.coe_pos] at h; exact h
    have ht'_lt_one : t' < 1 := by
      have h : (t':EReal) < 1 := by rw [← ht_eq]; exact ht_lt_one
      exact EReal.coe_lt_coe_iff.mp h
    let S : Set ℝ := {r ∈ Set.Icc (0:ℝ) 1 | binaryToTernary r ≤ t'}
    have h_set_eq : {x : EuclideanSpace' 1 | EuclideanSpace'.equiv_Real x ∈ Set.Icc 0 1 ∧ f_lifted x ≤ ↑t'} =
        Real.equiv_EuclideanSpace' '' S := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_image, S]
      constructor
      · intro ⟨h_in, hfx⟩
        use EuclideanSpace'.equiv_Real x
        refine ⟨⟨h_in, ?_⟩, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
        simp only [f_lifted] at hfx
        have h_max : max 0 (binaryToTernary (EuclideanSpace'.equiv_Real x)) ≤ t' := by
          rw [EReal.coe_le_coe_iff] at hfx; exact hfx
        exact le_of_max_le_right h_max
      · intro ⟨r, ⟨hr_in, hr_le⟩, hrx⟩
        constructor
        · rw [← hrx, EuclideanSpace'.equiv_Real.apply_symm_apply]; exact hr_in
        · rw [← hrx]; simp only [f_lifted, EuclideanSpace'.equiv_Real.apply_symm_apply]
          rw [EReal.coe_le_coe_iff]
          exact max_le (le_of_lt ht'_pos) hr_le
    rw [h_set_eq]
    have h_convex : Convex ℝ S := binaryToTernary_props.monotone_on.convex_le (convex_Icc 0 1) t'
    have h_bounded : Bornology.IsBounded S := (Metric.isBounded_Icc 0 1).subset (fun x hx => hx.1)
    have h_ordConnected : S.OrdConnected := Convex.ordConnected h_convex
    by_cases hS_empty : S = ∅
    · rw [hS_empty]; simp only [Set.image_empty]; exact LebesgueMeasurable.empty
    push_neg at hS_empty
    have h_zero_in_S : (0:ℝ) ∈ S := by
      simp only [S, Set.mem_Icc]
      constructor
      · exact ⟨le_refl 0, zero_le_one⟩
      · rw [binaryToTernary_props.zero_at_zero]; exact le_of_lt ht'_pos
    have h_bdd_above : BddAbove S := ⟨1, fun x hx => hx.1.2⟩
    let a := sSup S
    have ha_mem : a ∈ Set.Icc (0:ℝ) 1 := ⟨
      le_csSup_of_le h_bdd_above h_zero_in_S (le_refl 0),
      csSup_le (Set.nonempty_of_mem h_zero_in_S) (fun x hx => hx.1.2)⟩
    have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
      show Continuous (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
      exact continuous_induced_rng.mpr (continuous_pi (fun _ => continuous_id))
    have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
      exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) ⟨0, by decide⟩
    let e : ℝ ≃ₜ EuclideanSpace' 1 :=
      { toEquiv := Real.equiv_EuclideanSpace'
        continuous_toFun := hf_cont
        continuous_invFun := hg_cont }
    -- S is either [0, a] or [0, a) where a = sSup S; both are measurable
    have h_S_subset_Icc : S ⊆ Set.Icc 0 a := fun x hx => ⟨hx.1.1, le_csSup h_bdd_above hx⟩
    have h_image_Icc : Real.equiv_EuclideanSpace' '' Set.Icc 0 a =
        {x : EuclideanSpace' 1 | EuclideanSpace'.equiv_Real x ∈ Set.Icc 0 a} := by
      ext x; simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · intro ⟨r, hr, hrx⟩
        rw [← hrx, EuclideanSpace'.equiv_Real.apply_symm_apply]; exact hr
      · intro hx
        exact ⟨EuclideanSpace'.equiv_Real x, hx, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
    have h_meas_Icc : LebesgueMeasurable (Real.equiv_EuclideanSpace' '' Set.Icc 0 a) := by
      apply IsClosed.measurable; rw [h_image_Icc]
      exact IsClosed.preimage hg_cont isClosed_Icc
    by_cases ha_in_S : a ∈ S
    · -- S = [0, a]
      have h_S_eq : S = Set.Icc 0 a := by
        ext x
        constructor
        · intro hx; exact h_S_subset_Icc hx
        · intro hx
          exact h_ordConnected.out h_zero_in_S ha_in_S ⟨hx.1, hx.2⟩
      rw [h_S_eq]; exact h_meas_Icc
    · -- S = [0, a)
      have h_S_eq : S = Set.Ico 0 a := by
        ext x
        constructor
        · intro hx
          refine ⟨hx.1.1, ?_⟩
          rcases lt_or_eq_of_le (le_csSup h_bdd_above hx) with hlt | heq
          · exact hlt
          · exfalso; rw [heq] at hx; exact ha_in_S hx
        · intro hx
          have ⟨y, hy_in_S, hx_lt_y⟩ := exists_lt_of_lt_csSup (Set.nonempty_of_mem h_zero_in_S) hx.2
          exact h_ordConnected.out h_zero_in_S hy_in_S ⟨hx.1, le_of_lt hx_lt_y⟩
      rw [h_S_eq]
      have h_image_Ico : Real.equiv_EuclideanSpace' '' Set.Ico 0 a =
          {x : EuclideanSpace' 1 | EuclideanSpace'.equiv_Real x ∈ Set.Ico 0 a} := by
        ext x; simp only [Set.mem_image, Set.mem_setOf_eq]
        constructor
        · intro ⟨r, hr, hrx⟩
          rw [← hrx, EuclideanSpace'.equiv_Real.apply_symm_apply]; exact hr
        · intro hx
          exact ⟨EuclideanSpace'.equiv_Real x, hx, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
      -- [0, a) = [0, a] \ {a}
      have h_diff : Set.Ico 0 a = Set.Icc 0 a \ {a} := by
        ext x; simp only [Set.mem_Ico, Set.mem_diff, Set.mem_Icc, Set.mem_singleton_iff]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨⟨h1, le_of_lt h2⟩, ne_of_lt h2⟩
        · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, lt_of_le_of_ne h2 h3⟩
      rw [h_diff, Set.image_diff Real.equiv_EuclideanSpace'.injective, Set.diff_eq]
      apply LebesgueMeasurable.inter h_meas_Icc
      apply LebesgueMeasurable.complement
      apply IsNull.measurable
      exact Countable.Lebesgue_measure Nat.one_pos (Set.countable_singleton a |>.image _)

lemma f_lifted_measurable : UnsignedMeasurable f_lifted := by
  -- Apply Lemma 1.3.9(viii): f is measurable iff ∀ t, {x | f(x) ≤ t} is measurable
  have h_iff : UnsignedMeasurable f_lifted ↔ (∀ t, LebesgueMeasurable {x | f_lifted x ≤ t}) :=
    (UnsignedMeasurable.TFAE f_lifted_unsigned).out 1 8
  apply h_iff.mpr
  intro t
  rcases lt_trichotomy t 0 with ht_neg | ht_zero | ht_pos
  · have h_empty : {x | f_lifted x ≤ t} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le ht_neg (f_lifted_unsigned x)
    rw [h_empty]; exact LebesgueMeasurable.empty
  · subst ht_zero
    have h_eq : {x | f_lifted x ≤ (0 : EReal)} = {x | f_lifted x = 0} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hle; exact le_antisymm hle (f_lifted_unsigned x)
      · intro heq; rw [heq]
    rw [h_eq]; exact f_lifted_zero_set_measurable
  · rcases le_or_gt 1 t with ht_ge_one | ht_lt_one
    · have h_univ : {x | f_lifted x ≤ t} = Set.univ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact le_trans (f_lifted_le_one x) ht_ge_one
      rw [h_univ]; exact IsOpen.measurable isOpen_univ
    · exact sublevel_set_measurable t ht_pos ht_lt_one

/-- Non-measurable F ⊆ \[0,1\] with {name}`binaryToTernary`(F) ⊆ Cantor set (Vitali construction). -/
lemma exists_nonmeasurable_with_cantor_image :
    ∃ F : Set ℝ, ∃ A : Set ℝ, F ⊆ Set.Icc 0 1 ∧
    ¬ LebesgueMeasurable (Real.equiv_EuclideanSpace' '' F) ∧
    binaryToTernary '' F ⊆ CantorSet ∧
    F ⊆ A ∧
    A ⊆ Set.Icc 0 1 ∧
    (Set.Icc 0 1 \ A).Countable ∧
    Set.InjOn binaryToTernary A := by
  obtain ⟨A, hA_sub, hA_cocountable, hA_inj, hA_disjoint⟩ := binaryToTernary_props.injective_on_nonterminating
  let F := VitaliSet ∩ A
  use F, A
  refine ⟨?hF_sub, ?hF_nonmeas, ?hF_image, ?hF_sub_A, hA_sub, hA_cocountable, hA_inj⟩
  case hF_sub => intro x hx; exact VitaliSet_subset_unit_interval hx.1
  case hF_image =>
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx_in_Icc : x ∈ Set.Icc (0:ℝ) 1 := hA_sub hx.2
    have h_image := binaryToTernary_props.image_in_cantor ⟨x, hx_in_Icc, rfl⟩
    cases h_image with
    | inl h => exact h
    | inr h =>
      simp only [Set.mem_singleton_iff] at h
      exfalso
      have h_x_eq_0 : x = 0 := binaryToTernary_eq_zero_iff hx_in_Icc |>.mp h
      have h0_dyadic : (0:ℝ) ∈ DyadicRationals := ⟨0, 0, by norm_num, by norm_num⟩
      subst h_x_eq_0
      have h0_in_A : (0:ℝ) ∈ A := hx.2
      have h0_in_inter : (0:ℝ) ∈ A ∩ DyadicRationals := ⟨h0_in_A, h0_dyadic⟩
      rw [hA_disjoint] at h0_in_inter
      exact h0_in_inter
  case hF_nonmeas =>
    intro hF_meas
    have hV_decomp : VitaliSet = F ∪ (VitaliSet \ A) := by
      ext x; simp only [F, Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
      constructor
      · intro hx
        by_cases hxA : x ∈ A
        · left; exact ⟨hx, hxA⟩
        · right; exact ⟨hx, hxA⟩
      · intro hx; rcases hx with ⟨hx, _⟩ | ⟨hx, _⟩ <;> exact hx
    have hVminusA_countable : (VitaliSet \ A).Countable := by
      apply Set.Countable.mono _ hA_cocountable
      intro x hx; exact ⟨VitaliSet_subset_unit_interval hx.1, hx.2⟩
    have hVminusA_null : IsNull (Real.equiv_EuclideanSpace' '' (VitaliSet \ A)) :=
      Countable.Lebesgue_measure Nat.one_pos (Set.Countable.image hVminusA_countable _)
    have hVminusA_meas : LebesgueMeasurable (Real.equiv_EuclideanSpace' '' (VitaliSet \ A)) :=
      IsNull.measurable hVminusA_null
    have hV_meas : LebesgueMeasurable (Real.equiv_EuclideanSpace' '' VitaliSet) := by
      have h_image_union : Real.equiv_EuclideanSpace' '' VitaliSet =
          Real.equiv_EuclideanSpace' '' F ∪ Real.equiv_EuclideanSpace' '' (VitaliSet \ A) := by
        ext x
        simp only [Set.mem_image, Set.mem_union]
        constructor
        · intro ⟨r, hr, hrx⟩
          rw [hV_decomp] at hr
          rcases hr with ⟨hrV, hrA⟩ | ⟨hrV, hrA⟩
          · left; exact ⟨r, ⟨hrV, hrA⟩, hrx⟩
          · right; exact ⟨r, ⟨hrV, hrA⟩, hrx⟩
        · intro h
          rcases h with ⟨r, ⟨hrV, hrA⟩, hrx⟩ | ⟨r, ⟨hrV, hrA⟩, hrx⟩
          · exact ⟨r, hrV, hrx⟩
          · exact ⟨r, hrV, hrx⟩
      rw [h_image_union]; exact LebesgueMeasurable.union hF_meas hVminusA_meas
    exact VitaliSet.nonmeasurable hV_meas
  case hF_sub_A => intro x hx; exact hx.2

end Remark_1_3_10
