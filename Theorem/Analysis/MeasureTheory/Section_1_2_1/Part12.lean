import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Def.Analysis.MeasureTheory.Section_1_2_1.Part10
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


-- Helpers for theorem IsElementary.almost_disjoint
/-- Measure is additive on unions of elementary sets with disjoint interiors: μ(E ∪ F) = μ(E) + μ(F). -/
lemma IsElementary.measure_of_almostDisjUnion {d:ℕ} {E F: Set (EuclideanSpace' d)}
    (hE: IsElementary E) (hF: IsElementary F)
    (h: interior E ∩ interior F = ∅) :
    (hE.union hF).measure = hE.measure + hF.measure := by
  -- Strategy: Use decomposition E ∪ F = E ∪ (F \ E) which is disjoint,
  -- then show (F \ E).measure = hF.measure by using that E ∩ F has measure zero
  -- when interiors are disjoint.
  classical
  -- Step 1: Decompose E ∪ F = E ∪ (F \ E) (disjoint union)
  have h_union_decomp : E ∪ F = E ∪ (F \ E) := by
    ext x
    constructor
    · rintro (hx_E | hx_F)
      · exact Or.inl hx_E
      · by_cases hx_E : x ∈ E
        · exact Or.inl hx_E
        · exact Or.inr ⟨hx_F, hx_E⟩
    · rintro (hx_E | ⟨hx_F, _⟩)
      · exact Or.inl hx_E
      · exact Or.inr hx_F
  -- Step 2: F \ E is elementary and disjoint from E
  have hF_sdiff_E : IsElementary (F \ E) := IsElementary.sdiff hF hE
  have h_disj : Disjoint E (F \ E) := by
    rw [Set.disjoint_iff]
    intro x ⟨hx_E, _, hx_not_E⟩
    exact hx_not_E hx_E
  -- Step 3: Apply measure_of_disjUnion
  have h_decomp_measure : (hE.union hF_sdiff_E).measure = hE.measure + hF_sdiff_E.measure :=
    IsElementary.measure_of_disjUnion hE hF_sdiff_E h_disj
  -- Step 4: Show both unions represent the same set
  set T := (hE.union hF).partition.choose
  have hT_disj : (T : Set (Box d)).PairwiseDisjoint Box.toSet := (hE.union hF).partition.choose_spec.1
  have h_eq : E ∪ F = ⋃ B ∈ T, B.toSet := (hE.union hF).partition.choose_spec.2
  have h_measure_eq : (hE.union hF_sdiff_E).measure = (hE.union hF).measure := by
    rw [(hE.union hF_sdiff_E).measure_eq hT_disj (by rw [← h_union_decomp, h_eq]),
        (hE.union hF).measure_eq hT_disj h_eq]
  -- Step 5: Show (F \ E).measure = hF.measure when interiors are disjoint
  -- This follows because E ∩ F ⊆ frontier E ∪ frontier F, and the overlap has measure zero
  have h_sdiff_measure : hF_sdiff_E.measure = hF.measure := by
    -- By monotonicity: (F \ E).measure ≤ hF.measure (since F \ E ⊆ F)
    have h_mono : hF_sdiff_E.measure ≤ hF.measure :=
      IsElementary.measure_mono hF_sdiff_E hF (fun _ hx => hx.1)
    -- By additivity: hF.measure ≤ (E ∩ F).measure + (F \ E).measure
    -- But E ∩ F is elementary and has empty interior, so measure ≤ 0
    -- For disjoint interiors, we can show measure_mono in reverse direction
    have h_decomp_F : F = (E ∩ F) ∪ (F \ E) := by
      ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
      constructor
      · intro hx
        by_cases hxE : x ∈ E
        · exact Or.inl ⟨hxE, hx⟩
        · exact Or.inr ⟨hx, hxE⟩
      · rintro (⟨_, hx⟩ | ⟨hx, _⟩) <;> exact hx
    have h_disj_decomp : Disjoint (E ∩ F) (F \ E) := by
      rw [Set.disjoint_iff]
      intro x ⟨⟨hxE, _⟩, _, hxnE⟩
      exact hxnE hxE
    have hEF_inter : IsElementary (E ∩ F) := IsElementary.inter hE hF
    have h_F_measure : hF.measure = (hEF_inter.union hF_sdiff_E).measure := by
      set T_F := hF.partition.choose
      have hT_F_disj : (T_F : Set (Box d)).PairwiseDisjoint Box.toSet := hF.partition.choose_spec.1
      have hF_eq : F = ⋃ B ∈ T_F, B.toSet := hF.partition.choose_spec.2
      rw [(hEF_inter.union hF_sdiff_E).measure_eq hT_F_disj (by rw [← h_decomp_F, hF_eq]),
          hF.measure_eq hT_F_disj hF_eq]
    have h_union_add : (hEF_inter.union hF_sdiff_E).measure = hEF_inter.measure + hF_sdiff_E.measure :=
      IsElementary.measure_of_disjUnion hEF_inter hF_sdiff_E h_disj_decomp
    -- Key: show hEF_inter.measure = 0 when interior E ∩ interior F = ∅
    -- This requires showing that elementary sets with empty interior have measure zero
    have h_inter_empty_interior : interior (E ∩ F) = ∅ := by
      rw [interior_inter, h]
    -- For an elementary set with empty interior, all its partition boxes must be degenerate
    have h_inter_measure_zero : hEF_inter.measure = 0 := by
      set T_EF := hEF_inter.partition.choose
      have hT_EF_disj : (T_EF : Set (Box d)).PairwiseDisjoint Box.toSet := hEF_inter.partition.choose_spec.1
      have hEF_eq : E ∩ F = ⋃ B ∈ T_EF, B.toSet := hEF_inter.partition.choose_spec.2
      rw [hEF_inter.measure_eq hT_EF_disj hEF_eq]
      apply Finset.sum_eq_zero
      intro B hB
      -- Show B has empty interior and thus volume 0
      have hB_subset : B.toSet ⊆ E ∩ F := by
        rw [hEF_eq]
        exact Set.subset_biUnion_of_mem hB
      have hB_interior_empty : interior B.toSet = ∅ := by
        apply Set.eq_empty_of_subset_empty
        calc interior B.toSet ⊆ interior (E ∩ F) := interior_mono hB_subset
          _ = ∅ := h_inter_empty_interior
      -- Use that a box with empty interior has volume zero
      -- interior B = ∅ means some side has empty interior, i.e., is a single point or empty
      -- For a box, this means some BoundedInterval has a = b (degenerate)
      -- The interior of a box is empty iff some side interval has empty interior
      have hB_empty_or_degenerate : B.toSet = ∅ ∨ ∃ i, interior (B.side i).toSet = ∅ := by
        by_cases hB_nonempty : B.toSet.Nonempty
        · right
          by_contra h_all_nonempty
          push_neg at h_all_nonempty
          have : (Set.univ.pi fun i => interior (B.side i).toSet).Nonempty :=
            Set.univ_pi_nonempty_iff.mpr (fun i => h_all_nonempty i)
          rw [B.interior_toSet] at hB_interior_empty
          exact (this.preimage (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).surjective).ne_empty hB_interior_empty
        · left
          exact Set.not_nonempty_iff_eq_empty.mp hB_nonempty
      rcases hB_empty_or_degenerate with hB_empty | ⟨i, hi⟩
      · exact Box.volume_eq_zero_of_empty B hB_empty
      · -- A BoundedInterval with empty interior has length 0
        rw [Box.volume]
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        -- Show |B.side i|ₗ = 0 when interior (B.side i).toSet = ∅
        have h_length_zero : |B.side i|ₗ = 0 := by
          cases hI : B.side i with
          | Ioo a b =>
            simp only [hI, BoundedInterval.toSet, interior_Ioo, Set.Ioo_eq_empty_iff] at hi
            simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
            have hab : b ≤ a := le_of_not_gt hi
            simp only [max_eq_right (sub_nonpos.mpr hab)]
          | Icc a b =>
            simp only [hI, BoundedInterval.toSet, interior_Icc, Set.Ioo_eq_empty_iff] at hi
            simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
            have hab : b ≤ a := le_of_not_gt hi
            simp only [max_eq_right (sub_nonpos.mpr hab)]
          | Ioc a b =>
            simp only [hI, BoundedInterval.toSet, interior_Ioc, Set.Ioo_eq_empty_iff] at hi
            simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
            have hab : b ≤ a := le_of_not_gt hi
            simp only [max_eq_right (sub_nonpos.mpr hab)]
          | Ico a b =>
            simp only [hI, BoundedInterval.toSet, interior_Ico, Set.Ioo_eq_empty_iff] at hi
            simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
            have hab : b ≤ a := le_of_not_gt hi
            simp only [max_eq_right (sub_nonpos.mpr hab)]
        exact h_length_zero
    -- Now combine: hF.measure = 0 + hF_sdiff_E.measure = hF_sdiff_E.measure
    rw [h_F_measure, h_union_add, h_inter_measure_zero, zero_add]
  -- Final step: combine everything
  rw [← h_measure_eq, h_decomp_measure, h_sdiff_measure]

/-- Split a {lean}`Fin (n+1)` indexed union into a {lean}`Fin n` indexed union plus the last element.
    This is a general helper for induction on finite unions. -/
lemma Fin.iUnion_succ_eq_union_last {α : Type*} {n : ℕ} (f : Fin (n + 1) → Set α) :
    (⋃ i, f i) = (⋃ i : Fin n, f (Fin.castSucc i)) ∪ f (Fin.last n) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · intro ⟨i, hi⟩
    by_cases hlt : (i : ℕ) < n
    · left; exact ⟨⟨i, hlt⟩, by simp [Fin.castSucc]; exact hi⟩
    · right
      have : i = Fin.last n := Fin.ext (Nat.eq_of_lt_succ_of_not_lt i.isLt hlt)
      exact this ▸ hi
  · intro h
    rcases h with ⟨i, hi⟩ | h
    · exact ⟨Fin.castSucc i, hi⟩
    · exact ⟨Fin.last n, h⟩

/-- When boxes are pairwise almost-disjoint, restricting to the first n boxes preserves this. -/
lemma AlmostDisjoint.pairwise_castSucc {d n : ℕ} {B : Fin (n + 1) → Box d}
    (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) :
    Pairwise (Function.onFun AlmostDisjoint (fun i => B (Fin.castSucc i))) := by
  intro i j hij
  simp only [Function.onFun]
  apply hdisj
  simp [Fin.ext_iff]
  intro heq
  exact hij (Fin.ext heq)

/-- When boxes are pairwise almost-disjoint, any of the first n is almost-disjoint from the last. -/
lemma AlmostDisjoint.castSucc_last {d n : ℕ} {B : Fin (n + 1) → Box d}
    (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) (i : Fin n) :
    AlmostDisjoint (B (Fin.castSucc i)) (B (Fin.last n)) := by
  apply hdisj
  intro heq
  have h1 : (Fin.castSucc i).val < n := Fin.castSucc_lt_last i
  rw [heq] at h1
  simp at h1

/-- For any {name}`BoundedInterval`, interior (closure I) ⊆ closure (interior I).
    This holds because all interval types ({name}`BoundedInterval.Ioo`, {name}`BoundedInterval.Icc`, {name}`BoundedInterval.Ioc`, {name}`BoundedInterval.Ico`) have closure = {name}`BoundedInterval.Icc`
    and interior = {name}`BoundedInterval.Ioo`, so interior(closure(I)) = {name}`BoundedInterval.Ioo` ⊆ {name}`BoundedInterval.Icc` = closure(interior(I)). -/
lemma BoundedInterval.interior_closure_subset_closure_interior (I : BoundedInterval) :
    interior (closure (I : Set ℝ)) ⊆ closure (interior (I : Set ℝ)) := by
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.set_Ioo]
    by_cases hab : a < b
    · simp only [closure_Ioo (ne_of_lt hab), interior_Icc, interior_Ioo]
      exact Set.Ioo_subset_Icc_self
    · simp only [Set.Ioo_eq_empty hab, closure_empty, interior_empty]; exact Set.empty_subset _
  | Icc a b =>
    simp only [BoundedInterval.set_Icc]
    by_cases hab : a < b
    · simp only [closure_Icc, interior_Icc, closure_Ioo (ne_of_lt hab)]
      exact Set.Ioo_subset_Icc_self
    · simp only [interior_Icc, Set.Ioo_eq_empty hab, closure_Icc, closure_empty]
      exact Set.empty_subset _
  | Ioc a b =>
    simp only [BoundedInterval.set_Ioc]
    by_cases hab : a < b
    · simp only [closure_Ioc (ne_of_lt hab), interior_Icc, interior_Ioc, closure_Ioo (ne_of_lt hab)]
      exact Set.Ioo_subset_Icc_self
    · simp only [Set.Ioc_eq_empty hab, closure_empty, interior_empty]; exact Set.empty_subset _
  | Ico a b =>
    simp only [BoundedInterval.set_Ico]
    by_cases hab : a < b
    · simp only [closure_Ico (ne_of_lt hab), interior_Icc, interior_Ico, closure_Ioo (ne_of_lt hab)]
      exact Set.Ioo_subset_Icc_self
    · simp only [Set.Ico_eq_empty hab, closure_empty, interior_empty]; exact Set.empty_subset _

/-- For any box, the interior of its frontier is empty. This holds regardless of whether
    the box uses closed intervals ({name}`BoundedInterval.Icc`), open intervals ({name}`BoundedInterval.Ioo`), or half-open intervals,
    because the frontier of a box is a lower-dimensional set (union of faces). -/
lemma Box.interior_frontier_eq_empty {d : ℕ} (B : Box d) : interior (frontier B.toSet) = ∅ := by
  rw [Box.frontier_toSet, ← (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).preimage_interior]
  rw [frontier, closure_pi_set, interior_pi_set Set.finite_univ, Set.diff_eq,
      interior_inter, interior_pi_set Set.finite_univ, interior_compl, closure_pi_set]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  simp only [Set.mem_preimage] at hx
  have ⟨hx1, hx2⟩ := hx
  apply hx2
  exact Set.pi_mono (fun i _ => BoundedInterval.interior_closure_subset_closure_interior _) hx1

/-- The interior of a finite union of box frontiers is empty. This is because each box frontier
    is a closed set with empty interior, and we can apply {name}`interior_union_isClosed_of_interior_empty`
    iteratively. -/
lemma interior_iUnion_Box_frontier_eq_empty {d n : ℕ} (B : Fin n → Box d) :
    interior (⋃ i, frontier (B i).toSet) = ∅ := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.iUnion_succ_eq_union_last, Set.union_comm,
        interior_union_isClosed_of_interior_empty isClosed_frontier]
    · exact Box.interior_frontier_eq_empty (B (Fin.last m))
    · exact ih (fun i => B (Fin.castSucc i))

theorem IsElementary.almost_disjoint {d k:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) (B: Fin k → Box d) (hEB: E = ⋃ i, (B i).toSet) (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) : hE.measure = ∑ i, |B i|ᵥ := by
  induction k generalizing E with
  | zero =>
    -- E = ⋃ i : Fin 0, (B i).toSet = ∅, so hE.measure = 0 = ∑ i : Fin 0, ...
    simp_all
  | succ n ih =>
    -- Define B' : Fin n → Box d as the first n boxes, and B_last as the last
    let B' : Fin n → Box d := fun i => B (Fin.castSucc i)
    let E' : Set (EuclideanSpace' d) := ⋃ i : Fin n, (B' i).toSet
    let B_last := B (Fin.last n)

    -- Split E using the helper lemma
    have hE_split : E = E' ∪ B_last.toSet := by
      simp only [hEB, E', B', B_last]
      exact Fin.iUnion_succ_eq_union_last (fun i => (B i).toSet)

    -- Show B' is almost disjoint using helper
    have hdisj' : Pairwise (Function.onFun AlmostDisjoint B') :=
      AlmostDisjoint.pairwise_castSucc hdisj

    -- E' is elementary (finite union of boxes)
    have hE'_elem : IsElementary E' := by
      classical
      have h_eq : E' = ⋃ E ∈ (Finset.univ : Finset (Fin n)).image (fun i => (B' i).toSet), E := by
        ext x
        simp only [E', Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and, exists_prop]
        constructor
        · intro ⟨i, hi⟩; exact ⟨(B' i).toSet, ⟨i, rfl⟩, hi⟩
        · intro ⟨_, ⟨i, rfl⟩, hi⟩; exact ⟨i, hi⟩
      rw [h_eq]
      apply IsElementary.union'
      intro E hE
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hE
      obtain ⟨i, rfl⟩ := hE
      exact IsElementary.box _

    -- Apply induction hypothesis to get measure of E'
    have hE'_eq : E' = ⋃ i, (B' i).toSet := rfl
    have hE'_measure : hE'_elem.measure = ∑ i : Fin n, (B' i).volume := ih hE'_elem B' hE'_eq hdisj'

    -- B_last is elementary (single box)
    have hB_last_elem : IsElementary B_last.toSet := IsElementary.box B_last

    -- Each B' i is almost-disjoint from B_last using helper
    have h_almost_disj_last : ∀ i : Fin n, AlmostDisjoint (B' i) B_last :=
      fun i => AlmostDisjoint.castSucc_last hdisj i

    -- Show interior E' ∩ interior B_last = ∅ (almost-disjoint as sets)
    have h_interior_disj : interior E' ∩ interior B_last.toSet = ∅ := by
      rw [← interior_inter]
      have h_inter_eq : E' ∩ B_last.toSet = ⋃ i : Fin n, ((B' i).toSet ∩ B_last.toSet) := by
        simp only [E', Set.iUnion_inter]
      rw [h_inter_eq]
      -- Prove interior of union is empty
      apply Set.eq_empty_of_forall_notMem
      intro y hy
      rw [mem_interior_iff_mem_nhds] at hy
      obtain ⟨U, hU_sub, hU_open, hy_in_U⟩ := mem_nhds_iff.mp hy
      -- y ∈ interior B_last (since the union is contained in B_last)
      have hy_int_Blast : y ∈ interior B_last.toSet := by
        apply interior_mono (Set.iUnion_subset fun i => Set.inter_subset_right)
        rw [mem_interior_iff_mem_nhds]
        exact mem_nhds_iff.mpr ⟨U, hU_sub, hU_open, hy_in_U⟩
      -- Define U' = U ∩ interior B_last
      let U' := U ∩ interior B_last.toSet
      have hU'_open : IsOpen U' := hU_open.inter isOpen_interior
      have hU'_nonempty : U'.Nonempty := ⟨y, hy_in_U, hy_int_Blast⟩
      -- U' ⊆ ⋃ i, frontier (B' i) (each point is in some B' i but not its interior)
      have h_U'_in_frontier : U' ⊆ ⋃ i : Fin n, frontier (B' i).toSet := by
        intro z ⟨hz_U, hz_int_Blast⟩
        have hz_union : z ∈ ⋃ i : Fin n, ((B' i).toSet ∩ B_last.toSet) := hU_sub hz_U
        simp only [Set.mem_iUnion] at hz_union ⊢
        obtain ⟨i, hz_Bi, _⟩ := hz_union
        use i
        rw [frontier_eq_closure_inter_closure]
        refine ⟨subset_closure hz_Bi, ?_⟩
        rw [mem_closure_iff]
        intro V hV_open hz_V
        by_contra h_empty
        push_neg at h_empty
        rw [Set.eq_empty_iff_forall_notMem] at h_empty
        have hV_sub : V ⊆ (B' i).toSet := fun w hw => by
          by_contra h_not_in
          exact h_empty w ⟨hw, h_not_in⟩
        have hz_int_Bi : z ∈ interior (B' i).toSet := by
          rw [mem_interior_iff_mem_nhds]
          exact Filter.mem_of_superset (hV_open.mem_nhds hz_V) hV_sub
        have h_disj := h_almost_disj_last i
        rw [AlmostDisjoint, Set.eq_empty_iff_forall_notMem] at h_disj
        exact h_disj z ⟨hz_int_Bi, hz_int_Blast⟩
      -- Use the helper: finite union of box frontiers has empty interior
      have h_union_empty_int : interior (⋃ i : Fin n, frontier (B' i).toSet) = ∅ :=
        interior_iUnion_Box_frontier_eq_empty B'
      -- U' ⊆ set with empty interior, but U' is open nonempty. Contradiction!
      have : interior U' ⊆ interior (⋃ i : Fin n, frontier (B' i).toSet) := interior_mono h_U'_in_frontier
      rw [h_union_empty_int] at this
      exact Set.not_nonempty_empty ((Set.eq_empty_of_subset_empty this).symm ▸ (hU'_open.interior_eq ▸ hU'_nonempty))

    -- Apply measure additivity for almost-disjoint sets
    have h_union_elem : IsElementary (E' ∪ B_last.toSet) := hE'_elem.union hB_last_elem
    have h_measure_add : h_union_elem.measure = hE'_elem.measure + hB_last_elem.measure :=
      IsElementary.measure_of_almostDisjUnion hE'_elem hB_last_elem h_interior_disj
    have h_measure_eq : hE.measure = h_union_elem.measure :=
      IsElementary.measure_eq_of_set_eq hE h_union_elem hE_split
    have h_B_last_measure : hB_last_elem.measure = B_last.volume :=
      IsElementary.measure_of_box B_last

    -- Final computation
    rw [Fin.sum_univ_castSucc, h_measure_eq, h_measure_add, hE'_measure, h_B_last_measure]

/-- Restricting pairwise almost-disjoint from ℕ to {lean}`Fin N` preserves the property. -/
lemma AlmostDisjoint.restrict_fin {d : ℕ} {B : ℕ → Box d}
    (h : Pairwise (Function.onFun AlmostDisjoint B)) (N : ℕ) :
    Pairwise (Function.onFun AlmostDisjoint (fun i : Fin N => B i.val)) := by
  intro i j hij
  simp only [Function.onFun]
  apply h
  intro heq
  exact hij (Fin.ext heq)

/-- For nonneg Real sequences, if all partial sums are ≤ c (an {name}`EReal` bound), then {name}`tsum` ≤ c.
    This is the converse direction of {name}`EReal.finset_sum_le_tsum`. -/
lemma EReal.tsum_le_of_sum_range_le {f : ℕ → ℝ} {c : EReal}
    (hf : ∀ n, 0 ≤ f n) (h : ∀ N, (∑ i ∈ Finset.range N, f i : EReal) ≤ c) :
    ∑' n, (f n).toEReal ≤ c := by
  -- Convert to ENNReal where tsum_le_of_sum_range_le is available
  let g : ℕ → ENNReal := fun n => ENNReal.ofReal (f n)
  -- Show (f n).toEReal = (g n : EReal)
  have hf_eq : ∀ n, (f n).toEReal = (g n : EReal) := fun n => by
    simp only [g, EReal.coe_ennreal_ofReal, max_eq_left (hf n)]
  -- Rewrite tsum using term equality
  have h_tsum_eq : ∑' n, (f n).toEReal = (∑' n, g n : ENNReal).toEReal := by
    have h1 : ∑' n, (f n).toEReal = ∑' n, (g n : EReal) := tsum_congr hf_eq
    have h2 : ∑' n, (g n : EReal) = (∑' n, g n : ENNReal).toEReal := by
      let φ : ENNReal →+ EReal := {
        toFun := (↑·)
        map_zero' := by simp
        map_add' := EReal.coe_ennreal_add
      }
      have h_map : φ (∑' n, g n) = ∑' n, φ (g n) :=
        Summable.map_tsum (f := g) ENNReal.summable φ continuous_coe_ennreal_ereal
      exact h_map.symm
    exact h1.trans h2
  rw [h_tsum_eq]
  -- If c = ⊤, trivially true
  by_cases hc : c = ⊤
  · rw [hc]; exact le_top
  -- c ≥ 0 since it bounds nonneg partial sums
  have hc_nn : 0 ≤ c := by
    have h0 : (∑ i ∈ Finset.range 0, f i : EReal) ≤ c := h 0
    simp at h0; exact h0
  -- Get partial sum bounds in ENNReal
  have h_enn : ∀ N, ∑ i ∈ Finset.range N, g i ≤ c.toENNReal := by
    intro N
    have h_sum_eq : (∑ i ∈ Finset.range N, g i : ENNReal).toEReal = (∑ i ∈ Finset.range N, f i : EReal) := by
      rw [EReal.coe_ennreal_finset_sum]
      exact Finset.sum_congr rfl (fun n _ => (hf_eq n).symm)
    have h_le : (∑ i ∈ Finset.range N, g i : ENNReal).toEReal ≤ c := by rw [h_sum_eq]; exact h N
    rw [← EReal.coe_toENNReal hc_nn] at h_le
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mp h_le
  have h_tsum_enn : ∑' n, g n ≤ c.toENNReal := ENNReal.tsum_le_of_sum_range_le h_enn
  -- Convert back: ↑(∑' g) ≤ ↑(c.toENNReal) and c.toENNReal.toEReal = c (when 0 ≤ c)
  have h_coe_le : (∑' n, g n : ENNReal).toEReal ≤ (c.toENNReal).toEReal :=
    EReal.coe_ennreal_le_coe_ennreal_iff.mpr h_tsum_enn
  calc (∑' n, g n : ENNReal).toEReal ≤ (c.toENNReal).toEReal := h_coe_le
    _ = c := EReal.coe_toENNReal hc_nn

/-- Lemma 1.2.9 (Outer measure of countable unions of almost disjoint boxes).
    For pairwise almost disjoint boxes, m*(⋃ Bᵢ) = ∑' m*(Bᵢ) = ∑' |Bᵢ|. -/
theorem Lebesgue_outer_measure.union_of_almost_disjoint {d:ℕ} {B : ℕ → Box d} (h : Pairwise (Function.onFun AlmostDisjoint B)) :
    Lebesgue_outer_measure (⋃ i, (B i).toSet) = ∑' i, Lebesgue_outer_measure (B i).toSet := by
  -- Simplify: m*(Bᵢ) = |Bᵢ| for each box (Lemma 1.2.6 + measure_of_box)
  have h_box_measure : ∀ i, Lebesgue_outer_measure (B i).toSet = (B i).volume.toEReal := by
    intro i
    rw [Lebesgue_outer_measure.elementary _ (IsElementary.box (B i)),
        IsElementary.measure_of_box]
  simp_rw [h_box_measure]
  -- The proof establishes equality by showing both ≤ and ≥
  apply le_antisymm
  -- Upper bound: m*(⋃ Bᵢ) ≤ ∑' |Bᵢ| by countable subadditivity
  · calc Lebesgue_outer_measure (⋃ i, (B i).toSet)
        ≤ ∑' i, Lebesgue_outer_measure (B i).toSet := Lebesgue_outer_measure.union_le _
      _ = ∑' i, (B i).volume.toEReal := by simp_rw [h_box_measure]
  -- Lower bound: ∑' |Bᵢ| ≤ m*(⋃ Bᵢ) by taking limit of finite partial sums
  · -- For each N, the finite union ⋃ i : Fin N, (B i) is contained in ⋃ i, (B i)
    -- So m*(⋃ i : Fin N, (B i)) ≤ m*(⋃ i, (B i)) by monotonicity
    -- And m*(⋃ i : Fin N, (B i)) = ∑ i : Fin N, |B i| by IsElementary.almost_disjoint
    -- Taking N → ∞ gives the result

    -- Step 1: For each N, show finite partial sum ≤ outer measure
    have h_finite_le : ∀ N : ℕ, (∑ i : Fin N, (B i.val).volume : EReal) ≤
        Lebesgue_outer_measure (⋃ i, (B i).toSet) := by
      intro N
      -- The finite union is contained in the countable union
      have h_subset : (⋃ i : Fin N, (B i.val).toSet) ⊆ (⋃ i, (B i).toSet) := by
        apply Set.iUnion_subset
        intro i
        exact Set.subset_iUnion (fun n => (B n).toSet) i.val
      -- By monotonicity: m*(finite union) ≤ m*(countable union)
      have h_mono := Lebesgue_outer_measure.mono h_subset
      -- The finite union is elementary (union of boxes)
      have hElem : IsElementary (⋃ i : Fin N, (B i.val).toSet) :=
        IsElementary.iUnion_boxes (fun i : Fin N => B i.val)
      -- m*(finite union) = m(finite union) since it's elementary
      have h_elem_eq : Lebesgue_outer_measure (⋃ i : Fin N, (B i.val).toSet) = hElem.measure :=
        Lebesgue_outer_measure.elementary _ hElem
      -- Pairwise almost disjoint for Fin N
      have h_pw : Pairwise (Function.onFun AlmostDisjoint (fun i : Fin N => B i.val)) :=
        AlmostDisjoint.restrict_fin h N
      -- m(finite union) = ∑ |B i| by IsElementary.almost_disjoint
      have h_sum_eq : hElem.measure = ∑ i : Fin N, (B i.val).volume :=
        IsElementary.almost_disjoint hElem (fun i : Fin N => B i.val) rfl h_pw
      have h_coe_sum : (∑ i : Fin N, (B i.val).volume : EReal) = (∑ i : Fin N, (B i.val).volume : ℝ).toEReal := by
        rw [EReal.coe_finset_sum (fun i _ => Box.volume_nonneg (B i.val))]
      calc (∑ i : Fin N, (B i.val).volume : EReal)
          = ((∑ i : Fin N, (B i.val).volume : ℝ) : EReal) := h_coe_sum
        _ = (hElem.measure : EReal) := by rw [h_sum_eq]
        _ = Lebesgue_outer_measure (⋃ i : Fin N, (B i.val).toSet) := h_elem_eq.symm
        _ ≤ Lebesgue_outer_measure (⋃ i, (B i).toSet) := h_mono

    -- Step 2: Take limit - convert Fin N sum to Finset.range N sum and use EReal lemma
    have h_range_le : ∀ N : ℕ, (∑ i ∈ Finset.range N, (B i).volume : EReal) ≤
        Lebesgue_outer_measure (⋃ i, (B i).toSet) := by
      intro N
      have h_eq : (∑ i ∈ Finset.range N, ((B i).volume : EReal)) = (∑ i : Fin N, ((B i.val).volume : EReal)) := by
        conv_lhs => rw [← Fin.sum_univ_eq_sum_range (fun i => ((B i).volume : EReal)) N]
      rw [h_eq]
      exact h_finite_le N

    -- Step 3: Apply EReal.tsum_le_of_sum_range_le
    exact EReal.tsum_le_of_sum_range_le (fun n => Box.volume_nonneg (B n)) h_range_le

theorem Lebesgue_outer_measure.univ {d:ℕ} {hd: 0 < d} : Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) = ⊤ := by
  -- Strategy: Show m*(univ) ≥ N for any N by taking N disjoint unit boxes, hence m*(univ) = ⊤

  -- Define unit box at integer lattice point a
  let UnitBox : (Fin d → ℤ) → Box d := fun a => { side := fun i => Icc (a i : ℝ) ((a i : ℝ) + 1) }

  -- Each unit box has volume 1
  have h_vol : ∀ a : Fin d → ℤ, (UnitBox a).volume = 1 := by
    intro a
    simp only [Box.volume, UnitBox]
    simp only [BoundedInterval.length, BoundedInterval.b, BoundedInterval.a]
    simp only [add_sub_cancel_left]
    simp only [max_eq_left (by norm_num : (0:ℝ) ≤ 1)]
    simp only [Finset.prod_const_one]

  -- Unit boxes at different lattice points have disjoint interiors
  have h_almost_disj : ∀ a b : Fin d → ℤ, a ≠ b → AlmostDisjoint (UnitBox a) (UnitBox b) := by
    intro a b hab
    simp only [AlmostDisjoint]
    -- Interior of Icc-box is Ioo-box
    have h_int : ∀ c : Fin d → ℤ, interior (UnitBox c).toSet =
        {x | ∀ i, x i ∈ Set.Ioo (c i : ℝ) ((c i : ℝ) + 1)} := by
      intro c
      rw [Box.interior_toSet]
      ext x; simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_setOf_eq, UnitBox, BoundedInterval.toSet, interior_Icc]; rfl
    rw [h_int a, h_int b]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro ha hb
    apply hab
    funext i
    -- ha says: ∀ j, x j ∈ Ioo (a j) (a j + 1)
    -- So for coordinate i: a i < x i < a i + 1, meaning ⌊x i⌋ = a i
    have hai : x i ∈ Set.Ioo (a i : ℝ) ((a i : ℝ) + 1) := ha i
    have hbi : x i ∈ Set.Ioo (b i : ℝ) ((b i : ℝ) + 1) := hb i
    rw [Set.mem_Ioo] at hai hbi
    have ha_floor : (⌊x i⌋ : ℤ) = a i := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast hai.1.le
      · exact_mod_cast hai.2
    have hb_floor : (⌊x i⌋ : ℤ) = b i := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast hbi.1.le
      · exact_mod_cast hbi.2
    exact ha_floor.symm.trans hb_floor

  -- For any N, take N disjoint unit boxes (all with first coordinate 0,..,N-1, rest 0)
  have h_arb_large : ∀ N : ℕ, (N : EReal) ≤ Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) := by
    intro N
    -- Define N unit boxes at (0,0,...), (1,0,...), ..., (N-1,0,...)
    let pts : Fin N → (Fin d → ℤ) := fun n => fun i =>
      if i = ⟨0, hd⟩ then (n : ℤ) else 0
    -- These points are all distinct
    have h_pts_inj : Function.Injective pts := by
      intro m n hmn
      have : pts m ⟨0, hd⟩ = pts n ⟨0, hd⟩ := by rw [hmn]
      simp only [pts, ↓reduceIte] at this
      exact Fin.ext (Int.ofNat_injective this)
    -- The union of these N unit boxes is contained in univ
    have h_subset : (⋃ n : Fin N, (UnitBox (pts n)).toSet) ⊆ Set.univ := Set.subset_univ _
    -- By monotonicity
    -- The boxes are pairwise almost disjoint
    have h_pw : Pairwise (Function.onFun AlmostDisjoint (fun n : Fin N => UnitBox (pts n))) := by
      intro i j hij
      simp only [Function.onFun]
      apply h_almost_disj
      intro heq
      exact hij (h_pts_inj heq)
    -- Apply IsElementary.almost_disjoint for finite unions
    have hElem : IsElementary (⋃ n : Fin N, (UnitBox (pts n)).toSet) :=
      IsElementary.iUnion_boxes (fun n => UnitBox (pts n))

    -- N = ∑ |UnitBox| because each has volume 1
    have h_sum_vol : (∑ n : Fin N, (UnitBox (pts n)).volume) = N := by
      simp only [h_vol, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]

    -- ∑ volumes = measure of union (by IsElementary.almost_disjoint)
    have h_elem_eq : hElem.measure = ∑ n : Fin N, (UnitBox (pts n)).volume :=
      IsElementary.almost_disjoint hElem (fun n => UnitBox (pts n)) rfl h_pw

    calc (N : EReal)
        = ((N : ℕ) : ℝ) := (EReal.coe_coe_eq_natCast N).symm
      _ = ↑(∑ n : Fin N, (UnitBox (pts n)).volume) := by rw [h_sum_vol]
      _ = ↑hElem.measure := by rw [h_elem_eq]
      _ = Lebesgue_outer_measure (⋃ n : Fin N, (UnitBox (pts n)).toSet) := by
          rw [← Lebesgue_outer_measure.elementary _ hElem]
      _ ≤ Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) :=
          Lebesgue_outer_measure.mono h_subset

  -- Since m*(univ) ≥ N for all N, we have m*(univ) = ⊤
  rw [EReal.eq_top_iff_forall_lt]
  intro r
  -- Find N > r
  obtain ⟨N, hN⟩ := exists_nat_gt r
  calc (r : EReal) < (N : ℝ) := EReal.coe_lt_coe hN
    _ = (N : EReal) := EReal.coe_coe_eq_natCast N
    _ ≤ Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) := h_arb_large N

/-- Remark 1.2.10 -/
theorem Box.sum_volume_eq {d:ℕ} (B B': ℕ → Box d) (hdisj: Pairwise (Function.onFun AlmostDisjoint B)) (hdisj': Pairwise (Function.onFun AlmostDisjoint B')) (hcover: (⋃ n, (B n).toSet) = (⋃ n, (B' n).toSet)) :
    ∑' n, (B n).volume = ∑' n, (B' n).volume := by
  -- Establish outer measure equality using union_of_almost_disjoint (Lemma 1.2.9)
  have hB := Lebesgue_outer_measure.union_of_almost_disjoint hdisj
  have hB' := Lebesgue_outer_measure.union_of_almost_disjoint hdisj'
  -- Simplify: m*(Bᵢ) = |Bᵢ|.toEReal for each box
  have h_box : ∀ i, Lebesgue_outer_measure (B i).toSet = (B i).volume.toEReal := by
    intro i
    rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _), IsElementary.measure_of_box]
  have h_box' : ∀ i, Lebesgue_outer_measure (B' i).toSet = (B' i).volume.toEReal := by
    intro i
    rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _), IsElementary.measure_of_box]
  simp_rw [h_box] at hB
  simp_rw [h_box'] at hB'
  -- Now: ∑' |B n|.toEReal = m*(⋃ B n) = m*(⋃ B' n) = ∑' |B' n|.toEReal
  have h_eq : (∑' n, ((B n).volume : EReal)) = (∑' n, ((B' n).volume : EReal)) := by
    rw [← hB, hcover, hB']
  -- Define ENNReal versions and work through ENNReal
  have h_vol_nn : ∀ n, 0 ≤ (B n).volume := fun n => Box.volume_nonneg _
  have h_vol_nn' : ∀ n, 0 ≤ (B' n).volume := fun n => Box.volume_nonneg _
  let f : ℕ → ENNReal := fun n => ENNReal.ofReal (B n).volume
  let f' : ℕ → ENNReal := fun n => ENNReal.ofReal (B' n).volume
  -- Key: (B n).volume.toEReal = (f n : EReal) for nonneg volumes
  have hf_eq : ∀ n, ((B n).volume : EReal) = (f n : EReal) := fun n => by
    simp only [f, EReal.coe_ennreal_ofReal, max_eq_left (h_vol_nn n)]
  have hf'_eq : ∀ n, ((B' n).volume : EReal) = (f' n : EReal) := fun n => by
    simp only [f', EReal.coe_ennreal_ofReal, max_eq_left (h_vol_nn' n)]
  -- Rewrite h_eq using ENNReal
  simp_rw [hf_eq, hf'_eq] at h_eq
  -- ENNReal tsums commute with coercion to EReal
  have h_ennreal_eq : (∑' n, f n : ENNReal) = ∑' n, f' n := by
    have h_coe : ∀ (g : ℕ → ENNReal), (∑' n, g n : ENNReal).toEReal = ∑' n, (g n : EReal) := by
      intro g
      let φ : ENNReal →+ EReal := {
        toFun := (↑·)
        map_zero' := by simp
        map_add' := EReal.coe_ennreal_add
      }
      exact Summable.map_tsum ENNReal.summable φ continuous_coe_ennreal_ereal
    rw [← h_coe f, ← h_coe f'] at h_eq
    exact EReal.coe_ennreal_eq_coe_ennreal_iff.mp h_eq
  -- Transfer back to ℝ using ENNReal.toReal
  have h_toReal_eq : (∑' n, f n).toReal = (∑' n, f' n).toReal := by rw [h_ennreal_eq]
  -- Use ENNReal.tsum_toReal_eq for finite-valued functions
  have hf_ne_top : ∀ n, f n ≠ ⊤ := fun n => ENNReal.ofReal_ne_top
  have hf'_ne_top : ∀ n, f' n ≠ ⊤ := fun n => ENNReal.ofReal_ne_top
  rw [ENNReal.tsum_toReal_eq hf_ne_top, ENNReal.tsum_toReal_eq hf'_ne_top] at h_toReal_eq
  -- Simplify: (ENNReal.ofReal x).toReal = x for x ≥ 0
  simp only [f, f', ENNReal.toReal_ofReal (h_vol_nn _), ENNReal.toReal_ofReal (h_vol_nn' _)] at h_toReal_eq
  exact h_toReal_eq

