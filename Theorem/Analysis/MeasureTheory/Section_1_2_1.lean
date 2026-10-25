import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


/-- Express {name}`Box.toSet` as a preimage of a pi set under the {name}`PiLp` homeomorphism. -/
lemma Box.toSet_eq_ofLp_preimage {d : ℕ} (B : Box d) :
    B.toSet = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹' Set.univ.pi (fun i => (B.side i).toSet) := by
  ext x; simp only [Box.mem_toSet, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]; rfl

/-- The interior of {name}`Box.toSet` expressed as a preimage. -/
lemma Box.interior_toSet {d : ℕ} (B : Box d) :
    interior B.toSet = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
      Set.univ.pi (fun i => interior (B.side i).toSet) := by
  rw [Box.toSet_eq_ofLp_preimage,
    ← (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).preimage_interior,
    interior_pi_set Set.finite_univ]

/-- The closure of {name}`Box.toSet` expressed as a preimage. -/
lemma Box.closure_toSet {d : ℕ} (B : Box d) :
    closure B.toSet = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
      Set.univ.pi (fun i => closure (B.side i).toSet) := by
  rw [Box.toSet_eq_ofLp_preimage,
    ← (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).preimage_closure,
    closure_pi_set]

/-- The frontier of {name}`Box.toSet` expressed via the {name}`PiLp` homeomorphism. -/
lemma Box.frontier_toSet {d : ℕ} (B : Box d) :
    frontier B.toSet = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
      frontier (Set.univ.pi (fun i => (B.side i).toSet)) := by
  rw [Box.toSet_eq_ofLp_preimage,
    ← (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).preimage_frontier]

/-- A box with {name}`BoundedInterval.Icc` sides is closed. -/
lemma Box.isClosed_toSet_of_Icc {d : ℕ} (B : Box d)
    (h : ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) : IsClosed B.toSet := by
  rw [Box.toSet_eq_ofLp_preimage]
  apply IsClosed.preimage (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).continuous
  apply isClosed_set_pi; intro i _
  obtain ⟨a, b, hab⟩ := h i
  simp only [hab, BoundedInterval.toSet]; exact isClosed_Icc

/-- Exercise 1.2.3(i) (Empty set) -/
theorem Lebesgue_outer_measure.of_empty (d:ℕ) : Lebesgue_outer_measure (∅: Set (EuclideanSpace' d)) = 0 := by
  obtain rfl | hd := Nat.eq_zero_or_pos d
  · simp [Lebesgue_outer_measure_of_dim_zero]
  · exact Countable.Lebesgue_measure hd Set.countable_empty

/-- Exercise 1.2.3(ii) (Monotonicity) -/
theorem Lebesgue_outer_measure.mono {d: ℕ} {E F : Set (EuclideanSpace' d)} (h : E ⊆ F) :
    Lebesgue_outer_measure E ≤ Lebesgue_outer_measure F := by
  unfold Lebesgue_outer_measure
  refine sInf_le_sInf ?_
  rintro V ⟨X, S, hF, rfl⟩
  exact ⟨X, S, h.trans hF, rfl⟩

/-- Lebesgue outer measure is non-negative.
    Since it's the sInf of sums of box volumes, which are all ≥ 0, the result is ≥ 0. -/
theorem Lebesgue_outer_measure.nonneg {d: ℕ} (E : Set (EuclideanSpace' d)) :
    0 ≤ Lebesgue_outer_measure E := by
  unfold Lebesgue_outer_measure
  -- 0 ≤ sInf S when all elements are ≥ 0 (for complete lattice, sInf ∅ = ⊤ ≥ 0)
  apply le_sInf
  intro V hV
  obtain ⟨X, S, _, rfl⟩ := hV
  apply tsum_nonneg
  intro n
  -- Box volume is non-negative (product of nonneg lengths)
  have hvol : 0 ≤ |S n|ᵥ := by
    rw [Box.volume]
    apply Finset.prod_nonneg
    intro i _
    rw [BoundedInterval.length]
    exact le_max_right _ _
  exact EReal.coe_nonneg.mpr hvol

/-- Finite subadditivity -/
theorem Lebesgue_outer_measure.finite_union_le {d n:ℕ} (E: Fin n → Set (EuclideanSpace' d)) :
    Lebesgue_outer_measure (⋃ i, E i) ≤ ∑ i, Lebesgue_outer_measure (E i) := by
  -- Extend E to ℕ → Set by using empty set for indices ≥ n, then use countable subadditivity
  let E' : ℕ → Set (EuclideanSpace' d) := fun k =>
    if h : k < n then E ⟨k, h⟩ else ∅
  -- The union over Fin n equals the union over all k with E' k
  have h_union : (⋃ i, E i) = (⋃ k, E' k) := by
    ext x
    simp [E']
    constructor
    · intro ⟨i, hi⟩
      use i.val
      simp [hi]
    · intro ⟨k, hx⟩
      by_cases hk : k < n
      · use ⟨k, hk⟩
        simpa [dif_pos hk] using hx
      · simp [dif_neg hk] at hx
  rw [h_union]
  -- Apply countable subadditivity
  calc Lebesgue_outer_measure (⋃ k, E' k)
      ≤ ∑' k, Lebesgue_outer_measure (E' k) := union_le E'
    _ = ∑ i : Fin n, Lebesgue_outer_measure (E i) := by
        -- The sum over ℕ equals the sum over Fin n because E' k = ∅ for k ≥ n
        -- First, establish that E' k = ∅ for k ≥ n, so its outer measure is 0
        have h_empty : ∀ k ≥ n, E' k = ∅ := fun k hk => dif_neg (not_lt.mpr hk)
        have h_measure_empty : ∀ k ≥ n, Lebesgue_outer_measure (E' k) = 0 := by
          intro k hk
          rw [h_empty k hk, of_empty]

        -- Convert the tsum to a sum over Fin n
        -- The key lemma we need is: tsum equals finite sum when function has finite support
        -- In our case, E' k is non-empty only for k < n

        -- Define an explicit bijection and use it
        have : ∑' k, Lebesgue_outer_measure (E' k) = ∑ i : Fin n, Lebesgue_outer_measure (E' i.val) := by
          -- Use tsum_eq_sum with finite support
          let s : Finset ℕ := Finset.range n
          have h_support : ∀ k ∉ s, Lebesgue_outer_measure (E' k) = 0 := by
            intro k hk
            have : ¬ k < n := by simpa [s, Finset.mem_range] using hk
            exact h_measure_empty k (le_of_not_gt this)
          rw [tsum_eq_sum h_support]
          -- Now show the sums are equal by reindexing
          refine Finset.sum_bij (fun (k : ℕ) (hk : k ∈ s) => ⟨k, ?_⟩) ?_ ?_ ?_ ?_
          · simpa [s, Finset.mem_range] using hk
          · intros; simp
          · intros k₁ k₂ hk₁ hk₂ heq; simp at heq; exact heq
          · intro i _
            use i.val
            refine ⟨?_, ?_⟩
            · simp [s, Finset.mem_range, i.isLt]
            · simp
          · intro i _; simp

        rw [this]
        congr 1
        ext i
        simp [E', dif_pos i.isLt]

