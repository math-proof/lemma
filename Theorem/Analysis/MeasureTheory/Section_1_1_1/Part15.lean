import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Abbrev.Analysis.MeasureTheory.Section_1_1_1.Part6
open BoundedInterval

open Pointwise


/-- The measure equals the sum of volumes for any disjoint box partition of the set. -/
theorem IsElementary.measure_eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E)
  {T: Finset (Box d)} (hT: (T : Set (Box d)).PairwiseDisjoint Box.toSet)
  (heq : E = ⋃ B ∈ T, B.toSet):
  hE.measure = ∑ B ∈ T, |B|ᵥ := by
  apply Box.measure_uniq hE.partition.choose_spec.1 hT _
  rw [←heq, ←hE.partition.choose_spec.2]

lemma IsElementary.measure_nonneg {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) :
  0 ≤ hE.measure := by
  -- Strategy:
  -- 1. Unfold measure: hE.measure = ∑ B ∈ partition, |B|ᵥ
  -- 2. Show each |B|ᵥ ≥ 0: volume is product of lengths, each length = max(...) ≥ 0
  -- 3. Apply Finset.sum_nonneg: sum of non-negative terms is non-negative
  -- Step 1: Unfold measure definition
  rw [IsElementary.measure]
  -- Step 2: Show each |B|ᵥ ≥ 0 for B in the partition
  have hvol_nonneg : ∀ B ∈ hE.partition.choose, 0 ≤ |B|ᵥ := by
    intro B hB
    -- Volume is product of lengths
    rw [Box.volume]
    apply Finset.prod_nonneg
    intro i _
    -- Each length = max(...) ≥ 0
    rw [BoundedInterval.length]
    exact le_max_right _ _
  -- Step 3: Apply Finset.sum_nonneg with the fact from step 2
  exact Finset.sum_nonneg hvol_nonneg

/-- Measure is additive on disjoint elementary sets: μ(E ∪ F) = μ(E) + μ(F). -/
lemma IsElementary.measure_of_disjUnion {d:ℕ} {E F: Set (EuclideanSpace' d)}
(hE: IsElementary E) (hF: IsElementary F) (hdisj: Disjoint E F):
  (hE.union hF).measure = hE.measure + hF.measure := by
  -- Strategy:
  -- 1. Get partitions: T_E = hE.partition.choose, T_F = hF.partition.choose
  -- 2. Show T_E ∪ T_F is pairwise disjoint
  -- 3. Show E ∪ F = ⋃ B ∈ T_E ∪ T_F, B.toSet using partition properties
  -- 4. Use IsElementary.measure_eq to show (hE.union hF).measure = ∑ B ∈ T_E ∪ T_F, |B|ᵥ
  -- 5. Use Finset.sum_union to split: ∑ B ∈ T_E ∪ T_F, |B|ᵥ = ∑ B ∈ T_E, |B|ᵥ + ∑ B ∈ T_F, |B|ᵥ
  -- 6. Apply IsElementary.measure_eq to show hE.measure = ∑ B ∈ T_E, |B|ᵥ and hF.measure = ∑ B ∈ T_F, |B|ᵥ
  classical -- for axiom of choice
  -- Step 1: Get partitions
  set T_E := hE.partition.choose
  set T_F := hF.partition.choose
  have hT_E_disj : (T_E : Set (Box d)).PairwiseDisjoint Box.toSet := hE.partition.choose_spec.1
  have hT_F_disj : (T_F : Set (Box d)).PairwiseDisjoint Box.toSet := hF.partition.choose_spec.1
  have hE_eq : E = ⋃ B ∈ T_E, B.toSet := hE.partition.choose_spec.2
  have hF_eq : F = ⋃ B ∈ T_F, B.toSet := hF.partition.choose_spec.2
  -- Step 2: Show T_E ∪ T_F is pairwise disjoint
  have hT_union_disj : ((T_E ∪ T_F : Finset (Box d)) : Set (Box d)).PairwiseDisjoint Box.toSet := by
    rw [Set.pairwiseDisjoint_iff]
    intro B₁ hB₁ B₂ hB₂ hB₁B₂
    simp at hB₁ hB₂
    -- Helper: boxes from different partitions can't intersect (E and F are disjoint)
    have h_cross_disj : ∀ B_E ∈ T_E, ∀ B_F ∈ T_F, (B_E.toSet ∩ B_F.toSet).Nonempty → False := by
      intro B_E hB_E B_F hB_F h_intersect
      obtain ⟨x, hx₁, hx₂⟩ := h_intersect
      have : x ∈ E ∩ F := by
        constructor
        · rw [hE_eq]
          exact Set.mem_biUnion hB_E hx₁
        · rw [hF_eq]
          exact Set.mem_biUnion hB_F hx₂
      rw [Set.disjoint_iff] at hdisj
      exact Set.notMem_empty x (hdisj this)
    -- Case analysis on which partitions the boxes belong to
    obtain (hB₁_E | hB₁_F) := hB₁ <;> obtain (hB₂_E | hB₂_F) := hB₂
    · -- Both in T_E: use hT_E_disj
      rw [Set.pairwiseDisjoint_iff] at hT_E_disj
      exact hT_E_disj hB₁_E hB₂_E hB₁B₂
    · -- B₁ in T_E, B₂ in T_F: contradiction via h_cross_disj
      exact False.elim (h_cross_disj B₁ hB₁_E B₂ hB₂_F hB₁B₂)
    · -- B₁ in T_F, B₂ in T_E: contradiction via h_cross_disj (symmetric case)
      exact False.elim (h_cross_disj B₂ hB₂_E B₁ hB₁_F (Set.inter_comm B₁.toSet B₂.toSet ▸ hB₁B₂))
    · -- Both in T_F: use hT_F_disj
      rw [Set.pairwiseDisjoint_iff] at hT_F_disj
      exact hT_F_disj hB₁_F hB₂_F hB₁B₂
  -- Step 3: Show E ∪ F = ⋃ B ∈ T_E ∪ T_F, B.toSet
  have h_union_eq : E ∪ F = ⋃ B ∈ T_E ∪ T_F, B.toSet := by
    rw [hE_eq, hF_eq]
    ext x
    simp [Set.mem_union, Finset.mem_union]
    constructor
    · rintro (⟨B, hB, hx⟩ | ⟨B, hB, hx⟩)
      · exact ⟨B, Or.inl hB, hx⟩
      · exact ⟨B, Or.inr hB, hx⟩
    · rintro ⟨B, hB | hB, hx⟩
      · left; exact ⟨B, hB, hx⟩
      · right; exact ⟨B, hB, hx⟩
  -- Step 4: Use IsElementary.measure_eq
  have h_union_measure : (hE.union hF).measure = ∑ B ∈ T_E ∪ T_F, |B|ᵥ :=
    (hE.union hF).measure_eq hT_union_disj h_union_eq
  -- Step 5: Use Finset.sum_union_inter to split the sum
  have h_sum_split : ∑ B ∈ T_E ∪ T_F, |B|ᵥ = ∑ B ∈ T_E, |B|ᵥ + ∑ B ∈ T_F, |B|ᵥ := by
    rw [←Finset.sum_union_inter]
    suffices ∑ B ∈ T_E ∩ T_F, |B|ᵥ = 0 by
      simp [this]
    apply Finset.sum_eq_zero
    intro B hB
    simp [Finset.mem_inter] at hB
    obtain ⟨hB_E, hB_F⟩ := hB
    -- B is in both partitions, so B.toSet ⊆ E ∩ F = ∅
    have hB_subset_empty : B.toSet ⊆ ∅ := by
      have hB_E_subset : B.toSet ⊆ E := by
        rw [hE_eq]
        intro x hx
        exact Set.mem_biUnion hB_E hx
      have hB_F_subset : B.toSet ⊆ F := by
        rw [hF_eq]
        intro x hx
        exact Set.mem_biUnion hB_F hx
      have : B.toSet ⊆ E ∩ F := Set.subset_inter hB_E_subset hB_F_subset
      exact this.trans (Set.disjoint_iff_inter_eq_empty.1 hdisj).subset
    -- Since B.toSet ⊆ ∅, we have B.toSet = ∅, so volume is 0
    have hB_empty : B.toSet = ∅ := Set.subset_empty_iff.1 hB_subset_empty
    exact Box.volume_eq_zero_of_empty B hB_empty
  -- Step 6: Apply IsElementary.measure_eq to individual measures
  have hE_measure : hE.measure = ∑ B ∈ T_E, |B|ᵥ := hE.measure_eq hT_E_disj hE_eq
  have hF_measure : hF.measure = ∑ B ∈ T_F, |B|ᵥ := hF.measure_eq hT_F_disj hF_eq
  -- Combine everything
  rw [h_union_measure, h_sum_split, hE_measure, hF_measure]

-- Helper lemmas for measure_of_disjUnion'

/-- Two different proofs that a set is elementary yield the same measure. -/
lemma IsElementary.measure_irrelevant {d:ℕ} {E: Set (EuclideanSpace' d)}
    (h₁ h₂ : IsElementary E) : h₁.measure = h₂.measure := by
  classical
  -- Use the partition data packaged inside h₂
  obtain ⟨h_pair, h_union⟩ := h₂.partition.choose_spec
  -- Evaluate both measures via the same partition
  have h₁_exp := h₁.measure_eq h_pair h_union
  have h₂_exp := h₂.measure_eq h_pair h_union
  simp [h₂_exp] at h₁_exp
  assumption

/-- If two elementary sets are equal, their measures are equal. -/
lemma IsElementary.measure_eq_of_set_eq {d:ℕ} {E F: Set (EuclideanSpace' d)}
    (hE: IsElementary E) (hF: IsElementary F) (h: E = F) :
    hE.measure = hF.measure := by
  subst h  -- Now both proofs describe the same set
  exact IsElementary.measure_irrelevant hE hF

/-- The union over an empty finset of elementary sets is the empty set. -/
lemma IsElementary.union'_empty_eq {d:ℕ} :
    (⋃ E ∈ (∅ : Finset (Set (EuclideanSpace' d))), E) = ∅ := by
  simp

open Classical in
/-- Measure of a sum over {lean}`insert a S'` equals the measure of {lean}`a` plus the measure of the sum over {lean}`S'`. -/
lemma IsElementary.sum_insert_split {d:ℕ} {a: Set (EuclideanSpace' d)} {S': Finset (Set (EuclideanSpace' d))}
    (ha : a ∉ S')
    (hE: ∀ E ∈ insert a S', IsElementary E) :
    ∑ E:(insert a S' : Finset (Set (EuclideanSpace' d))), (hE E.val E.property).measure =
    (hE a (Finset.mem_insert_self _ _)).measure +
    ∑ E:S', (hE E.val (Finset.mem_insert_of_mem E.property)).measure := by
  induction S' using Finset.induction_on with
  | empty =>
    letI : Unique (↥(insert a (∅ : Finset (Set (EuclideanSpace' d))))) := {
      default := ⟨a, by simp⟩
      uniq := fun ⟨x, hx⟩ => by
        apply Subtype.ext
        simpa using hx
    }
    rw [Fintype.sum_unique, Fintype.sum_empty, add_zero]
  | @insert b S'' hb_notin ih =>
    -- Inductive case: S' = insert b S''
    -- Goal: ∑ E:(insert a (insert b S'')), ... = measure(a) + ∑ E:(insert b S''), ...
    -- Use simp to expand both sides
    simp [hb_notin]
    -- Now split the sum on the LHS using Finset.sum_insert
    -- First split out a
    have ha_ne_b : a ≠ b := by simp_all
    have ha_notin_S'' : a ∉ S'' := by simp_all
    rw [Finset.sum_insert (by simp [ha_ne_b, ha_notin_S''])]
    -- Now split out b from the remaining sum
    rw [Finset.sum_insert (by simp [hb_notin])]
    -- Both sides should now match
    simp

/-- Measure is additive on pairwise disjoint finsets of elementary sets. -/
lemma IsElementary.measure_of_disjUnion' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, IsElementary E) (hdisj: (S : Set (Set (EuclideanSpace' d))).PairwiseDisjoint id):
  (IsElementary.union' hE).measure = ∑ E:S, (hE E.val E.property).measure := by
  -- Strategy: Induction on S. Base: empty set gives 0 = 0. Step: split S = insert a S',
  -- show union = a ∪ (union S'), prove a disjoint from union S' via pairwise disjointness,
  -- apply two-set additivity, use IH for S', combine.
  classical
  -- Induction on S using Finset.induction_on to reduce to two-set case
  induction S using Finset.induction_on with
  | empty =>
    -- Base case: S = ∅, both sides are 0
    have h_set_eq := IsElementary.union'_empty_eq (d := d)
    have h_measure_eq : (IsElementary.union' hE).measure = (IsElementary.empty d).measure :=
      IsElementary.measure_eq_of_set_eq (IsElementary.union' hE) (IsElementary.empty d) h_set_eq
    rw [h_measure_eq]
    -- Show (IsElementary.empty d).measure = 0
    have h_empty_measure : (IsElementary.empty d).measure = 0 := by
      have h_empty_eq : (∅ : Set (EuclideanSpace' d)) = ⋃ B ∈ (∅ : Finset (Box d)), B.toSet := by simp
      have h_empty_disj : ((∅ : Finset (Box d)) : Set (Box d)).PairwiseDisjoint Box.toSet := by simp
      rw [(IsElementary.empty d).measure_eq h_empty_disj h_empty_eq]
      simp [Finset.sum_empty]
    rw [h_empty_measure]
    simp [Finset.sum_empty]
  | @insert a S' ha_notin ih =>
    -- Extract hypotheses for S' and element a
    have hE_S' : ∀ E ∈ S', IsElementary E := by
      intro E hE_mem
      exact hE E (Finset.mem_insert_of_mem hE_mem)
    have hdisj_S' : Set.PairwiseDisjoint (S' : Set (Set (EuclideanSpace' d))) id := by
      intro E₁ hE₁ E₂ hE₂ hne
      apply hdisj
      · simp [hE₁]
      · simp [hE₂]
      · exact hne
    have hE_a : IsElementary a := hE a (Finset.mem_insert_self _ _)

    -- Show the union over insert a S' equals a ∪ (union over S')
    have h_union_split : ⋃ E ∈ insert a S', E = a ∪ (⋃ E ∈ S', E) := by
      ext x
      simp [Set.mem_iUnion, Set.mem_union, Finset.mem_insert]

    -- Prove a is disjoint from the union over S'
    have h_disj : Disjoint a (⋃ E ∈ S', E) := by
      rw [Set.disjoint_iff]
      intro x ⟨hx_a, hx_rest⟩
      simp [Set.mem_iUnion] at hx_rest
      obtain ⟨E, hE_mem, hx_E⟩ := hx_rest
      -- Use hdisj to show a and E are disjoint
      have h_disj_a_E : Disjoint a E := by
        have ha_mem : a ∈ ((insert a S' : Finset _) : Set _) := by simp
        have hE_mem' : E ∈ ((insert a S' : Finset _) : Set _) := by simp [hE_mem]
        have hne : a ≠ E := by
          intro h; subst h
          exact ha_notin hE_mem
        -- hdisj: (insert a S').toSet.PairwiseDisjoint id means distinct sets are disjoint
        -- Rewrite to extract the disjointness property
        rw [Set.pairwiseDisjoint_iff] at hdisj
        -- After rewriting, hdisj says: for distinct i, j in the set, (id i ∩ id j).Nonempty → i = j
        -- We have x ∈ a and x ∈ E, so (id a ∩ id E).Nonempty, which would give a = E
        -- But we also have hne : a ≠ E, so this is a contradiction
        have h_inter_nonempty : (id a ∩ id E).Nonempty := by
          simp [id]
          exact ⟨x, hx_a, hx_E⟩
        have h_eq := hdisj ha_mem hE_mem' h_inter_nonempty
        -- h_eq says a = E, but we have hne : a ≠ E, contradiction
        exact (hne h_eq).elim
      rw [Set.disjoint_iff] at h_disj_a_E
      exact h_disj_a_E ⟨hx_a, hx_E⟩

    -- Apply the two-set additivity lemma
    let hE_rest : IsElementary (⋃ E ∈ S', E) := IsElementary.union' hE_S'
    have h_two_set : (hE_a.union hE_rest).measure = hE_a.measure + hE_rest.measure :=
      IsElementary.measure_of_disjUnion hE_a hE_rest h_disj

    -- Equate the union witness measure with the two-set union measure
    have h_measure_eq : (IsElementary.union' hE).measure = (hE_a.union hE_rest).measure :=
      IsElementary.measure_eq_of_set_eq (IsElementary.union' hE) (hE_a.union hE_rest) h_union_split

    -- Split the sum into measure of a plus sum over S'
    have h_sum_split := IsElementary.sum_insert_split ha_notin hE
    -- Apply inductive hypothesis to the union over S', reconciling proof differences
    have h_ih_applied : hE_rest.measure = ∑ E : S', (hE_S' E.val E.property).measure := ih hE_S' hdisj_S'
    -- hE_S' is defined as hE_S' E hE_mem = hE E (Finset.mem_insert_of_mem hE_mem),
    -- so the sums are definitionally equal and we can use h_ih_applied directly
    have h_ih_adjusted : hE_rest.measure = ∑ E : S', (hE E.val (Finset.mem_insert_of_mem E.property)).measure :=
      h_ih_applied

    -- Combine all equalities to finish
    rw [h_measure_eq, h_two_set, h_sum_split]
    congr 1

/-- The empty set has measure zero. -/
@[simp]
lemma IsElementary.measure_of_empty (d:ℕ) : (IsElementary.empty d).measure = 0 := by
  -- Strategy: Use empty partition T = ∅, apply measure_eq, simplify with Finset.sum_empty
  classical
  have h_empty_eq : (∅ : Set (EuclideanSpace' d)) = ⋃ B ∈ (∅ : Finset (Box d)), B.toSet := by
    simp
  have h_empty_disj : ((∅ : Finset (Box d)) : Set (Box d)).PairwiseDisjoint Box.toSet := by
    simp
  rw [(IsElementary.empty d).measure_eq h_empty_disj h_empty_eq]
  simp [Finset.sum_empty]

/-- The measure of a single box equals its volume. -/
@[simp]
lemma IsElementary.measure_of_box {d:ℕ} (B: Box d) : (IsElementary.box B).measure = |B|ᵥ := by
  -- Strategy: Use singleton partition T = {B}, apply measure_eq, simplify with Finset.sum_singleton
  classical
  have h_box_eq : B.toSet = ⋃ B' ∈ ({B} : Finset (Box d)), B'.toSet := by
    simp
  have h_box_disj : (({B} : Finset (Box d)) : Set (Box d)).PairwiseDisjoint Box.toSet := by
    rw [Set.pairwiseDisjoint_iff]
    intro B₁ hB₁ B₂ hB₂ hB₁B₂
    simp at hB₁ hB₂
    -- For a singleton, B₁ = B₂ = B, so the condition is vacuously satisfied
    rw [hB₁, hB₂]
  rw [(IsElementary.box B).measure_eq h_box_disj h_box_eq]
  simp [Finset.sum_singleton]

/-- Elementary measure is monotone: if E ⊆ F then μ(E) ≤ μ(F). -/
lemma IsElementary.measure_mono  {d:ℕ} {E F: Set (EuclideanSpace' d)}
(hE: IsElementary E) (hF: IsElementary F) (hcont: E ⊆ F):
  hE.measure ≤ hF.measure := by
  -- Strategy using set difference:
  -- 1. Decompose F = E ∪ (F \ E) (disjoint since E ⊆ F)
  -- 2. Show F \ E is elementary via IsElementary.sdiff
  -- 3. Apply measure_of_disjUnion: hF.measure = hE.measure + (F \ E).measure
  -- 4. Use measure_nonneg: (F \ E).measure ≥ 0, so hE.measure ≤ hF.measure
  -- Step 1: Decompose F = E ∪ (F \ E)
  have hF_decomp : F = E ∪ (F \ E) := by
    ext x
    constructor
    · intro hx; by_cases hx_E : x ∈ E
      · left; exact hx_E
      · right; exact ⟨hx, hx_E⟩
    · intro h; obtain (hx_E | ⟨hx, _⟩) := h
      · exact hcont hx_E
      · exact hx
  -- Step 2: Show F \ E is elementary and disjoint from E
  have hF_sdiff_E : IsElementary (F \ E) := IsElementary.sdiff hF hE
  have h_disj : Disjoint E (F \ E) := by
    rw [Set.disjoint_iff]; intro x ⟨hx_E, _, hx_not_E⟩; exact hx_not_E hx_E
  -- Step 3: Apply measure_of_disjUnion
  have h_union_measure : (hE.union hF_sdiff_E).measure = hE.measure + hF_sdiff_E.measure :=
    IsElementary.measure_of_disjUnion hE hF_sdiff_E h_disj
  -- Step 4: Show that (hE.union hF_sdiff_E) and hF represent the same set F
  classical
  set T_F := hF.partition.choose
  have hT_F_disj : (T_F : Set (Box d)).PairwiseDisjoint Box.toSet := hF.partition.choose_spec.1
  have hF_eq : F = ⋃ B ∈ T_F, B.toSet := hF.partition.choose_spec.2
  have h_union_eq_partition : E ∪ (F \ E) = ⋃ B ∈ T_F, B.toSet := by rw [← hF_decomp, hF_eq]
  -- Step 5: Use measure_eq to show (hE.union hF_sdiff_E).measure = hF.measure
  have h_union_measure_eq : (hE.union hF_sdiff_E).measure = hF.measure := by
    rw [(hE.union hF_sdiff_E).measure_eq hT_F_disj h_union_eq_partition, hF.measure_eq hT_F_disj hF_eq]
  -- Step 6: Combine with measure_nonneg
  rw [← h_union_measure_eq, h_union_measure]
  linarith [IsElementary.measure_nonneg hF_sdiff_E]

/-- Subadditivity of measure on unions: μ(E ∪ F) ≤ μ(E) + μ(F). -/
lemma IsElementary.measure_of_union {d:ℕ} {E F: Set (EuclideanSpace' d)}
(hE: IsElementary E) (hF: IsElementary F):
  (hE.union hF).measure ≤ hE.measure + hF.measure := by
  -- Strategy (using Exercise 1.1.1):
  -- 1. Decompose E ∪ F = E ∪ (F \ E) (disjoint union)
  -- 2. Use IsElementary.sdiff (Exercise 1.1.1) to show F \ E is elementary
  -- 3. Apply measure_of_disjUnion: (hE.union hF_sdiff_E).measure = hE.measure + (F \ E).measure
  -- 4. Show (hE.union hF) and (hE.union hF_sdiff_E) represent the same set E ∪ F
  -- 5. Apply measure_mono: (F \ E).measure ≤ hF.measure since F \ E ⊆ F
  -- 6. Combine: (hE.union hF).measure = hE.measure + (F \ E).measure ≤ hE.measure + hF.measure
  -- Step 1: Decompose E ∪ F = E ∪ (F \ E)
  have h_union_decomp : E ∪ F = E ∪ (F \ E) := by
    ext x
    constructor
    · rintro (hx_E | hx_F); exact Or.inl hx_E
      by_cases hx_E : x ∈ E; exact Or.inl hx_E; exact Or.inr ⟨hx_F, hx_E⟩
    · rintro (hx_E | ⟨hx_F, _⟩); exact Or.inl hx_E; exact Or.inr hx_F
  -- Step 2-3: Use IsElementary.sdiff and apply measure_of_disjUnion
  have hF_sdiff_E : IsElementary (F \ E) := IsElementary.sdiff hF hE
  have h_disj : Disjoint E (F \ E) := by
    rw [Set.disjoint_iff]; intro x ⟨hx_E, _, hx_not_E⟩; exact hx_not_E hx_E
  have h_union_measure : (hE.union hF_sdiff_E).measure = hE.measure + hF_sdiff_E.measure :=
    IsElementary.measure_of_disjUnion hE hF_sdiff_E h_disj
  -- Step 4: Show both unions represent the same set E ∪ F
  classical
  set T := (hE.union hF).partition.choose
  have hT_disj : (T : Set (Box d)).PairwiseDisjoint Box.toSet := (hE.union hF).partition.choose_spec.1
  have h_eq : E ∪ F = ⋃ B ∈ T, B.toSet := (hE.union hF).partition.choose_spec.2
  have h_union_measure_eq : (hE.union hF_sdiff_E).measure = (hE.union hF).measure := by
    rw [(hE.union hF_sdiff_E).measure_eq hT_disj (by rw [← h_union_decomp, h_eq]),
        (hE.union hF).measure_eq hT_disj h_eq]
  -- Step 5-6: Apply measure_mono and combine
  have h_mono : hF_sdiff_E.measure ≤ hF.measure :=
    IsElementary.measure_mono hF_sdiff_E hF (fun _ hx => hx.1)
  rw [← h_union_measure_eq, h_union_measure]
  linarith

/-- Subadditivity of measure on finset unions: μ(⋃ S) ≤ ∑ μ(E) for E ∈ S. -/
lemma IsElementary.measure_of_union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, IsElementary E) :
  (IsElementary.union' hE).measure ≤ ∑ E:S, (hE E.val E.property).measure := by
  -- Strategy: Induction on S mirroring measure_of_disjUnion' but with inequality
  classical
  induction S using Finset.induction_on with
  | empty =>
    -- Base case: S = ∅, both sides are 0
    have h_set_eq := IsElementary.union'_empty_eq (d := d)
    have h_measure_eq : (IsElementary.union' hE).measure = (IsElementary.empty d).measure :=
      IsElementary.measure_eq_of_set_eq (IsElementary.union' hE) (IsElementary.empty d) h_set_eq
    simp [IsElementary.measure_of_empty]
  | @insert a S' ha_notin ih =>
    -- Extract hypotheses for S' and element a
    have hE_S' : ∀ E ∈ S', IsElementary E := fun E hE_mem => hE E (Finset.mem_insert_of_mem hE_mem)
    have hE_a : IsElementary a := hE a (Finset.mem_insert_self _ _)
    -- Show the union over insert a S' equals a ∪ (union over S')
    have h_union_split : ⋃ E ∈ insert a S', E = a ∪ (⋃ E ∈ S', E) := by
      ext x; simp [Set.mem_iUnion, Set.mem_union, Finset.mem_insert]
    -- Apply the two-set subadditivity lemma
    let hE_rest : IsElementary (⋃ E ∈ S', E) := IsElementary.union' hE_S'
    have h_two_set : (hE_a.union hE_rest).measure ≤ hE_a.measure + hE_rest.measure :=
      IsElementary.measure_of_union hE_a hE_rest
    -- Equate the union witness measure with the two-set union measure
    have h_measure_eq : (IsElementary.union' hE).measure = (hE_a.union hE_rest).measure :=
      IsElementary.measure_eq_of_set_eq (IsElementary.union' hE) (hE_a.union hE_rest) h_union_split
    -- Split the sum into measure of a plus sum over S'
    have h_sum_split := IsElementary.sum_insert_split ha_notin hE
    -- Apply inductive hypothesis
    have h_ih : hE_rest.measure ≤ ∑ E : S', (hE_S' E.val E.property).measure := ih hE_S'
    have h_ih_adjusted : hE_rest.measure ≤ ∑ E : S', (hE E.val (Finset.mem_insert_of_mem E.property)).measure :=
      h_ih
    -- Combine: (union' hE).measure = (hE_a.union hE_rest).measure ≤ hE_a.measure + hE_rest.measure
    --          ≤ hE_a.measure + ∑ E:S', ... = ∑ E:(insert a S'), ...
    rw [h_measure_eq, h_sum_split]
    linarith [h_two_set, h_ih_adjusted]

/-- Helper: Translation preserves interval length -/
lemma BoundedInterval.length_of_translate (I: BoundedInterval) (c: ℝ) :
  ∃ I' : BoundedInterval, I'.toSet = I.toSet + {c} ∧ |I'|ₗ = |I|ₗ := by
  cases I with
  | Ioo a b => use Ioo (a + c) (b + c); constructor <;> simp [toSet, BoundedInterval.length]
  | Icc a b => use Icc (a + c) (b + c); constructor <;> simp [toSet, BoundedInterval.length]
  | Ioc a b => use Ioc (a + c) (b + c); constructor <;> simp [toSet, BoundedInterval.length]
  | Ico a b => use Ico (a + c) (b + c); constructor <;> simp [toSet, BoundedInterval.length]

/-- Helper: Translation preserves box volume -/
lemma Box.volume_of_translate {d:ℕ} (B: Box d) (x: EuclideanSpace' d) :
  ∃ B' : Box d, B'.toSet = B.toSet + {x} ∧ |B'|ᵥ = |B|ᵥ := by
  -- Strategy:
  -- 1. For each coordinate i, translate B.side i by x i using length_of_translate
  -- 2. Construct B' with translated intervals: B'.side i = translated interval
  -- 3. Show B'.toSet = B.toSet + {x}: y ∈ B'.toSet ↔ y - x ∈ B.toSet (coordinate-wise)
  -- 4. Show |B'|ᵥ = |B|ᵥ: product of lengths, each length preserved by translation
  -- Step 1: For each coordinate i, get translated interval
  choose I' hI' using fun i ↦ BoundedInterval.length_of_translate (B.side i) (x i)
  -- Step 2: Construct B' with translated intervals
  use ⟨fun i ↦ I' i⟩
  constructor
  -- Step 3: Show B'.toSet = B.toSet + {x}
  · ext y
    simp only [Box.mem_toSet]
    constructor
    · intro hy
      apply Set.mem_add.mpr
      refine ⟨.toLp 2 (fun i ↦ y i - x i), ?_, x, rfl, by apply PiLp.ext; intro i; simp⟩
      simp only [Box.mem_toSet]; intro i
      have : y i ∈ (I' i).toSet := hy i
      rw [(hI' i).1] at this
      obtain ⟨a, ha, b, rfl, hab⟩ := this
      convert ha using 1; linarith
    · intro hy
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hy
      rw [Set.mem_singleton_iff.mp hb] at hab
      simp only [Box.mem_toSet] at ha
      intro i
      rw [(hI' i).1]
      exact Set.mem_add.mpr ⟨a i, ha i, x i, rfl, by have := congr_fun (congrArg WithLp.ofLp hab) i; simpa using this⟩
  -- Step 4: Show |B'|ᵥ = |B|ᵥ
  · simp [Box.volume]
    congr 1
    ext i
    exact (hI' i).2

/-- Translation is injective on sets: if S₁ + \{x\} = S₂ + \{x\}, then S₁ = S₂ -/
lemma Set.translate_inj {d:ℕ} (x: EuclideanSpace' d) (S₁ S₂ : Set (EuclideanSpace' d))
  (h_eq : S₁ + {x} = S₂ + {x}) : S₁ = S₂ := by
  ext y
  constructor
  · intro hy
    have : y + x ∈ S₁ + {x} := Set.mem_add.mpr ⟨y, hy, x, Set.mem_singleton x, rfl⟩
    rw [h_eq] at this
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp this
    rw [Set.mem_singleton_iff.mp hb] at hab
    exact (add_right_cancel hab) ▸ ha
  · intro hy
    have : y + x ∈ S₂ + {x} := Set.mem_add.mpr ⟨y, hy, x, Set.mem_singleton x, rfl⟩
    rw [← h_eq] at this
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp this
    rw [Set.mem_singleton_iff.mp hb] at hab
    exact (add_right_cancel hab) ▸ ha

/-- Elementary measure is translation-invariant: μ(E + \{x\}) = μ(E). -/
lemma IsElementary.measure_of_translate {d:ℕ} {E: Set (EuclideanSpace' d)}
(hE: IsElementary E) (x: EuclideanSpace' d):
  (hE.translate x).measure = hE.measure := by
  -- Strategy:
  -- 0. Case split: E = ∅ or E ≠ ∅
  --    a. Empty case: E = ∅ → E + {x} = ∅, both measures are 0
  --    b. Nonempty case: E ≠ ∅, proceed with partition translation
  -- 1. Get partition T of E: E = ⋃ B ∈ T, B.toSet (from hE.partition)
  -- 2. For each B ∈ T, use Box.volume_of_translate to get B' with B'.toSet = B.toSet + {x} and |B'|ᵥ = |B|ᵥ
  -- 3. Construct T' = {B' | B ∈ T} (using choose to get the translated boxes)
  -- 4. Show T' is pairwise disjoint (translation preserves disjointness)
  -- 5. Show E + {x} = ⋃ B' ∈ T', B'.toSet (translation distributes over union)
  -- 6. Apply measure_eq: (hE.translate x).measure = ∑ B' ∈ T', |B'|ᵥ = ∑ B ∈ T, |B|ᵥ = hE.measure
  classical
  by_cases h_empty : E = ∅
  · -- Empty case: E = ∅ → E + {x} = ∅, both measures are 0
    subst h_empty
    simp [IsElementary.measure_of_empty]
  · -- Nonempty case: E ≠ ∅
    -- Step 1: Get partition T of E, then filter to nonempty boxes
    set T := hE.partition.choose
    have hT_disj : (T : Set (Box d)).PairwiseDisjoint Box.toSet := hE.partition.choose_spec.1
    have hE_eq : E = ⋃ B ∈ T, B.toSet := hE.partition.choose_spec.2
    -- Filter to nonempty boxes only (empty boxes contribute 0 to measure anyway)
    set T := T.filter (fun B => B.toSet.Nonempty) with hT_def
    have hT_disj : (T : Set (Box d)).PairwiseDisjoint Box.toSet := by
      intro B₁ hB₁ B₂ hB₂ hB₁B₂
      simp only [Finset.mem_coe] at hB₁ hB₂
      exact hE.partition.choose_spec.1 (Finset.mem_of_mem_filter B₁ hB₁) (Finset.mem_of_mem_filter B₂ hB₂) hB₁B₂
    have hE_eq : E = ⋃ B ∈ T, B.toSet := by
      rw [hE_eq]
      ext y; simp
      constructor
      · intro ⟨B, hB, hy⟩
        exact ⟨B, Finset.mem_filter.mpr ⟨hB, ⟨y, hy⟩⟩, hy⟩
      · intro ⟨B, hB, hy⟩
        exact ⟨B, Finset.mem_of_mem_filter B hB, hy⟩
    have hT_nonempty : ∀ B ∈ T, B.toSet.Nonempty := by
      intro B hB
      exact (Finset.mem_filter.mp hB).2
    -- Step 2-3: Construct translated partition T'
    choose f hf using fun B : Box d => Box.volume_of_translate B x
    set T' := T.image f
    have hf_spec : ∀ B ∈ T, (f B).toSet = B.toSet + {x} ∧ |f B|ᵥ = |B|ᵥ := fun B hB => hf B
    -- Helper: f is injective on T (all boxes in T are nonempty by construction)
    have hf_inj : ∀ B₁ B₂, B₁ ∈ T → B₂ ∈ T → f B₁ = f B₂ → B₁ = B₂ := by
      intro B₁ B₂ hB₁ hB₂ h_eq
      have h_set_eq' : B₁.toSet = B₂.toSet :=
        Set.translate_inj x _ _ ((hf_spec B₁ hB₁).1.symm.trans ((congr_arg Box.toSet h_eq).trans (hf_spec B₂ hB₂).1))
      -- Since B₁ is in filtered T, it's nonempty, and B₁.toSet = B₂.toSet
      have h_inter_nonempty : (B₁.toSet ∩ B₂.toSet).Nonempty := by
        rw [h_set_eq', Set.inter_self]
        rw [← h_set_eq']
        exact hT_nonempty B₁ hB₁
      rw [Set.pairwiseDisjoint_iff] at hT_disj
      exact hT_disj hB₁ hB₂ h_inter_nonempty
    -- Step 4: Show T' is pairwise disjoint
    have hT'_disj : (T' : Set (Box d)).PairwiseDisjoint Box.toSet := by
      rw [Set.pairwiseDisjoint_iff]
      intro B₁' hB₁' B₂' hB₂' hB₁'B₂'
      simp [T'] at hB₁' hB₂'
      obtain ⟨B₁, hB₁, rfl⟩ := hB₁'
      obtain ⟨B₂, hB₂, rfl⟩ := hB₂'
      by_cases h_eq : f B₁ = f B₂
      · exact h_eq
      · -- If f B₁ ≠ f B₂ but they intersect, then B₁ = B₂ (contradiction)
        have h_translate_inter : (f B₁).toSet ∩ (f B₂).toSet = (B₁.toSet ∩ B₂.toSet) + {x} := by
          rw [(hf_spec B₁ hB₁).1, (hf_spec B₂ hB₂).1]
          ext y; simp only [Set.mem_inter_iff, Set.mem_add]
          constructor
          · rintro ⟨⟨a₁, ha₁, b₁, hb₁, hab₁⟩, ⟨a₂, ha₂, b₂, hb₂, hab₂⟩⟩
            have hb₁_eq : b₁ = x := Set.mem_singleton_iff.mp hb₁
            have hb₂_eq : b₂ = x := Set.mem_singleton_iff.mp hb₂
            rw [hb₁_eq] at hab₁
            rw [hb₂_eq] at hab₂
            exact ⟨a₁, ⟨ha₁, add_right_cancel (hab₁.trans hab₂.symm) ▸ ha₂⟩, x, Set.mem_singleton x, hab₁⟩
          · rintro ⟨a, ⟨ha₁, ha₂⟩, b, hb, hab⟩
            rw [Set.mem_singleton_iff.mp hb] at hab
            exact ⟨⟨a, ha₁, x, Set.mem_singleton x, hab⟩, ⟨a, ha₂, x, Set.mem_singleton x, hab⟩⟩
        have h_B_nonempty : (B₁.toSet ∩ B₂.toSet).Nonempty := by
          rw [h_translate_inter] at hB₁'B₂'
          obtain ⟨y, hy⟩ := hB₁'B₂'
          obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hy
          exact ⟨a, ha.1, ha.2⟩
        rw [Set.pairwiseDisjoint_iff] at hT_disj
        exact (h_eq (congr_arg f (hT_disj hB₁ hB₂ h_B_nonempty))).elim
    -- Step 5: Show E + {x} = ⋃ B' ∈ T', B'.toSet
    have h_union_eq : E + {x} = ⋃ B' ∈ T', B'.toSet := by
      rw [hE_eq]
      ext y; constructor
      · intro hy
        rw [Set.mem_iUnion₂]
        obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hy
        rw [Set.mem_iUnion₂] at ha
        obtain ⟨B, hB, haB⟩ := ha
        rw [Set.mem_singleton_iff.mp hb] at hab
        exact ⟨f B, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
          by rw [(hf_spec B hB).1]; exact Set.mem_add.mpr ⟨a, haB, x, rfl, hab⟩⟩
      · intro hy
        rw [Set.mem_iUnion₂] at hy
        obtain ⟨B', hB', hyB'⟩ := hy
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB'
        rw [(hf_spec B hB).1] at hyB'
        obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hyB'
        rw [Set.mem_singleton_iff.mp hb] at hab
        exact Set.mem_add.mpr ⟨a, Set.mem_iUnion₂.mpr ⟨B, hB, ha⟩, x, rfl, hab⟩
    -- Step 6: Apply measure_eq and show sum equality
    have h_translate_measure : (hE.translate x).measure = ∑ B' ∈ T', |B'|ᵥ :=
      (hE.translate x).measure_eq hT'_disj h_union_eq
    have h_sum_eq : ∑ B' ∈ T', |B'|ᵥ = ∑ B ∈ T, |B|ᵥ := by
      rw [Finset.sum_image (fun B₁ hB₁ B₂ hB₂ h_eq => hf_inj B₁ B₂ hB₁ hB₂ h_eq)]
      exact Finset.sum_congr rfl fun B hB => (hf_spec B hB).2
    rw [h_translate_measure, h_sum_eq, hE.measure_eq hT_disj hE_eq]

