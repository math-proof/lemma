import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
import Theorem.Analysis.Misc.NatBitwise
import Def.Analysis.MeasureTheory.Section_1_3_1.Part6


namespace UnsignedSimpleFunction.IntegralWellDef

open scoped Classical

/-- Core lemma: Two representations of the same function give the same weighted measure sum.
    This is the heart of Lemma 1.3.4 (Venn diagram argument). -/
lemma weightedMeasureSum_eq_of_eq {d k k' : ℕ}
    {c : Fin k → EReal} {E : Fin k → Set (EuclideanSpace' d)}
    {c' : Fin k' → EReal} {E' : Fin k' → Set (EuclideanSpace' d)}
    (hmes : ∀ i, LebesgueMeasurable (E i)) (hmes' : ∀ i, LebesgueMeasurable (E' i))
    (hnonneg : ∀ i, c i ≥ 0) (hnonneg' : ∀ i, c' i ≥ 0)
    (heq : ∑ i, (c i) • (EReal.indicator (E i)) = ∑ i, (c' i) • (EReal.indicator (E' i))) :
    weightedMeasureSum c E = weightedMeasureSum c' E' := by
  -- The proof uses the Venn diagram/atom argument
  -- 1. For any x in a non-empty atom A_n, evaluate heq at x:
  --    sum_{i : x ∈ E_i} c_i = sum_{j : x ∈ E'_j} c'_j
  -- 2. The membership in E_i for x ∈ A_n is determined by bit i of n
  -- 3. Multiply by m(A_n) and sum over all atoms
  -- 4. Swap order of summation to get the result

  -- Define atom measures
  let atomMeas : Fin (2^(k+k')) → EReal := fun n => Lebesgue_measure (atom E E' n)

  -- Atoms are measurable
  have hatom_mes : ∀ n, LebesgueMeasurable (atom E E' n) := atom_measurable hmes hmes'

  -- Step 1: For any point in an atom, the pointwise sums are equal
  have hpoint : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n,
      ∑ i : Fin k, (c i) * (EReal.indicator (E i) x) = ∑ i : Fin k', (c' i) * (EReal.indicator (E' i) x) := by
    intro n x hx
    have := congr_fun heq x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this

  -- Step 2: In atom n, membership in E_i is determined by bit i
  have hmem_E : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n, ∀ i : Fin k,
      (x ∈ E i) ↔ atomMembership k k' n i := by
    intro n x hx i
    exact (hx.1 i).symm

  have hmem_E' : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n, ∀ i : Fin k',
      (x ∈ E' i) ↔ atomMembership k k' n (k + i) := by
    intro n x hx i
    exact (hx.2 i).symm

  -- Step 3: The pointwise sum simplifies based on bit pattern
  have hsum_simp : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n,
      ∑ i : Fin k, (c i) * (EReal.indicator (E i) x) = ∑ i : Fin k, if atomMembership k k' n i then c i else 0 := by
    intro n x hx
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : atomMembership k k' n i
    · simp only [h]
      have hx_in : x ∈ E i := (hmem_E n x hx i).mpr h
      exact indicator_mul_mem (E i) (c i) x hx_in
    · simp only [h]
      have hx_out : x ∉ E i := fun hc => h ((hmem_E n x hx i).mp hc)
      exact indicator_mul_not_mem (E i) (c i) x hx_out

  have hsum_simp' : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n,
      ∑ i : Fin k', (c' i) * (EReal.indicator (E' i) x) = ∑ i : Fin k', if atomMembership k k' n (k + i) then c' i else 0 := by
    intro n x hx
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : atomMembership k k' n (k + i)
    · simp only [h]
      have hx_in : x ∈ E' i := (hmem_E' n x hx i).mpr h
      exact indicator_mul_mem (E' i) (c' i) x hx_in
    · simp only [h]
      have hx_out : x ∉ E' i := fun hc => h ((hmem_E' n x hx i).mp hc)
      exact indicator_mul_not_mem (E' i) (c' i) x hx_out

  -- Step 4: For non-empty atoms, the bit-pattern sums are equal
  have hbit_eq : ∀ n : Fin (2^(k+k')), (atom E E' n).Nonempty →
      (∑ i : Fin k, if atomMembership k k' n i = true then c i else 0 : EReal) =
      (∑ i : Fin k', if atomMembership k k' n (k + i) = true then c' i else 0 : EReal) := by
    intro n ⟨x, hx⟩
    rw [← hsum_simp n x hx, ← hsum_simp' n x hx]
    exact hpoint n x hx

  -- Step 5: E_i = union of atoms where bit i = 1
  have hE_decomp : ∀ i : Fin k, E i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n i}, atom E E' n :=
    fun i => set_eq_biUnion_atoms E E' i

  -- Step 6: Use finite additivity (this requires showing atoms are disjoint and measurable)
  -- m(E_i) = sum over atoms where bit i = 1 of m(atom)
  have hmes_decomp : ∀ i : Fin k, Lebesgue_measure (E i) =
      ∑ n : Fin (2^(k+k')), if atomMembership k k' n i then atomMeas n else 0 := by
    intro i
    -- Define a modified atom family: atom' n = atom n if bit i is 1, else ∅
    let atom' : Fin (2^(k+k')) → Set (EuclideanSpace' d) := fun n =>
      if atomMembership k k' n i then atom E E' n else ∅
    -- E i = ⋃ n, atom' n (because atoms with bit 0 contribute nothing)
    have hE_eq : E i = ⋃ n, atom' n := by
      rw [hE_decomp i]
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro ⟨n, hn, hx⟩
        use n
        simp only [atom', hn, ite_true]
        exact hx
      · intro ⟨n, hx⟩
        simp only [atom'] at hx
        by_cases hn : atomMembership k k' n i
        · simp only [hn, ite_true] at hx
          exact ⟨n, hn, hx⟩
        · simp only [hn] at hx
          exact False.elim hx
    -- atom' is pairwise disjoint
    have hdisj' : Set.univ.PairwiseDisjoint atom' := by
      intro i₁ _ i₂ _ hi
      simp only [Function.onFun, atom']
      by_cases h1 : atomMembership k k' i₁ i <;> by_cases h2 : atomMembership k k' i₂ i
      · simp only [h1, h2, ite_true]
        exact atom_pairwiseDisjoint E E' (by trivial : i₁ ∈ Set.univ) (by trivial) hi
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; intro _ _; simp
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; simp
      · simp only [h1, h2]
        rw [Set.disjoint_left]; simp
    -- atom' is measurable
    have hmes'_atom : ∀ n, LebesgueMeasurable (atom' n) := by
      intro n
      simp only [atom']
      by_cases h : atomMembership k k' n i
      · simp only [h, ite_true]; exact hatom_mes n
      · simp only [h]; exact LebesgueMeasurable.empty
    -- Apply finite additivity
    calc Lebesgue_measure (E i) = Lebesgue_measure (⋃ n, atom' n) := by rw [hE_eq]
      _ = ∑' n, Lebesgue_measure (atom' n) := Lebesgue_measure.finite_union hmes'_atom hdisj'
      _ = ∑ n : Fin (2^(k+k')), Lebesgue_measure (atom' n) := tsum_fintype _
      _ = ∑ n : Fin (2^(k+k')), if atomMembership k k' n i then atomMeas n else 0 := by
          congr 1; funext n; simp only [atom']
          by_cases h : atomMembership k k' n i
          · simp only [h, ite_true]; rfl
          · simp only [h]; exact Lebesgue_measure.empty

  have hE'_decomp : ∀ i : Fin k', E' i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n (k + i)}, atom E E' n :=
    fun i => set_eq_biUnion_atoms' E E' i

  have hmes_decomp' : ∀ i : Fin k', Lebesgue_measure (E' i) =
      ∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then atomMeas n else 0 := by
    intro i
    let atom'' : Fin (2^(k+k')) → Set (EuclideanSpace' d) := fun n =>
      if atomMembership k k' n (k + i) then atom E E' n else ∅
    have hE'_eq : E' i = ⋃ n, atom'' n := by
      rw [hE'_decomp i]
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro ⟨n, hn, hx⟩
        use n
        simp only [atom'', hn, ite_true]
        exact hx
      · intro ⟨n, hx⟩
        simp only [atom''] at hx
        by_cases hn : atomMembership k k' n (k + i)
        · simp only [hn, ite_true] at hx
          exact ⟨n, hn, hx⟩
        · simp only [hn] at hx
          exact False.elim hx
    have hdisj'' : Set.univ.PairwiseDisjoint atom'' := by
      intro i₁ _ i₂ _ hi
      simp only [Function.onFun, atom'']
      by_cases h1 : atomMembership k k' i₁ (k + i) <;> by_cases h2 : atomMembership k k' i₂ (k + i)
      · simp only [h1, h2, ite_true]
        exact atom_pairwiseDisjoint E E' (by trivial : i₁ ∈ Set.univ) (by trivial) hi
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; intro _ _; simp
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; simp
      · simp only [h1, h2]
        rw [Set.disjoint_left]; simp
    have hmes''_atom : ∀ n, LebesgueMeasurable (atom'' n) := by
      intro n
      simp only [atom'']
      by_cases h : atomMembership k k' n (k + i)
      · simp only [h, ite_true]; exact hatom_mes n
      · simp only [h]; exact LebesgueMeasurable.empty
    calc Lebesgue_measure (E' i) = Lebesgue_measure (⋃ n, atom'' n) := by rw [hE'_eq]
      _ = ∑' n, Lebesgue_measure (atom'' n) := Lebesgue_measure.finite_union hmes''_atom hdisj''
      _ = ∑ n : Fin (2^(k+k')), Lebesgue_measure (atom'' n) := tsum_fintype _
      _ = ∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then atomMeas n else 0 := by
          congr 1; funext n; simp only [atom'']
          by_cases h : atomMembership k k' n (k + i)
          · simp only [h, ite_true]; rfl
          · simp only [h]; exact Lebesgue_measure.empty

  -- Step 7: Compute weightedMeasureSum using decomposition
  calc weightedMeasureSum c E
      = ∑ i : Fin k, (c i) * Lebesgue_measure (E i) := rfl
    _ = ∑ i : Fin k, (c i) * (∑ n : Fin (2^(k+k')), if atomMembership k k' n i then atomMeas n else 0) := by
        congr 1; ext i; congr 1; exact hmes_decomp i
    _ = ∑ i : Fin k, ∑ n : Fin (2^(k+k')), (c i) * (if atomMembership k k' n i then atomMeas n else 0) := by
        congr 1; ext i
        -- c i * sum = sum of c i * each term
        have hf_nonneg : ∀ n : Fin (2^(k+k')), 0 ≤ (if atomMembership k k' n i then atomMeas n else 0) := by
          intro n
          split_ifs
          · exact Lebesgue_outer_measure.nonneg _
          · rfl
        exact EReal.mul_finset_sum_of_nonneg (2^(k+k')) (c i) (fun n => if atomMembership k k' n i then atomMeas n else 0) hf_nonneg
    _ = ∑ i : Fin k, ∑ n : Fin (2^(k+k')), if atomMembership k k' n i then (c i) * atomMeas n else 0 := by
        congr 1; ext i; congr 1; ext n
        split_ifs <;> simp
    _ = ∑ n : Fin (2^(k+k')), ∑ i : Fin k, if atomMembership k k' n i then (c i) * atomMeas n else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ n : Fin (2^(k+k')), atomMeas n * (∑ i : Fin k, if atomMembership k k' n i then c i else 0) := by
        congr 1; ext n
        -- Factoring: ∑ i, if p then c i * m else 0 = m * ∑ i, if p then c i else 0
        have hc_nonneg : ∀ i : Fin k, 0 ≤ (if atomMembership k k' n i then c i else 0) := fun i => by
          split_ifs; exact hnonneg i; rfl
        rw [EReal.mul_finset_sum_of_nonneg k (atomMeas n) _ hc_nonneg]
        congr 1; ext i
        split_ifs with h
        · -- c i * atomMeas n = atomMeas n * c i
          exact (EReal.mul_comm (atomMeas n) (c i)).symm
        · simp
    _ = ∑ n : Fin (2^(k+k')), atomMeas n * (∑ i : Fin k', if atomMembership k k' n (k + i) then c' i else 0) := by
        congr 1; ext n
        by_cases h : (atom E E' n).Nonempty
        · congr 1; exact hbit_eq n h
        · -- Empty atom has measure 0, so this term is 0
          rw [Set.not_nonempty_iff_eq_empty] at h
          have hzero : atomMeas n = 0 := by
            simp only [atomMeas, h, Lebesgue_measure.empty]
          simp only [hzero, zero_mul]
    _ = ∑ n : Fin (2^(k+k')), ∑ i : Fin k', if atomMembership k k' n (k + i) then (c' i) * atomMeas n else 0 := by
        congr 1; ext n
        -- Expanding: m * ∑ i, if p then c i else 0 = ∑ i, if p then c i * m else 0
        have hc'_nonneg : ∀ i : Fin k', 0 ≤ (if atomMembership k k' n (k + i) then c' i else 0) := fun i => by
          split_ifs; exact hnonneg' i; rfl
        rw [EReal.mul_finset_sum_of_nonneg k' (atomMeas n) _ hc'_nonneg]
        congr 1; ext i
        split_ifs with h
        · exact EReal.mul_comm (atomMeas n) (c' i)
        · simp
    _ = ∑ i : Fin k', ∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then (c' i) * atomMeas n else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ i : Fin k', (c' i) * (∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then atomMeas n else 0) := by
        congr 1; ext i
        -- c' i * sum = sum of c' i * each term, then distribute through conditionals
        have hf_nonneg : ∀ n : Fin (2^(k+k')), 0 ≤ (if atomMembership k k' n (k + i) then atomMeas n else 0) := by
          intro n
          split_ifs
          · exact Lebesgue_outer_measure.nonneg _
          · rfl
        rw [EReal.mul_finset_sum_of_nonneg (2^(k+k')) (c' i) _ hf_nonneg]
        congr 1; ext n
        split_ifs <;> simp
    _ = ∑ i : Fin k', (c' i) * Lebesgue_measure (E' i) := by
        congr 1; ext i; congr 1; exact (hmes_decomp' i).symm
    _ = weightedMeasureSum c' E' := rfl

end UnsignedSimpleFunction.IntegralWellDef
