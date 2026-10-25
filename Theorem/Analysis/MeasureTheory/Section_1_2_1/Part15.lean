import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Def.Analysis.MeasureTheory.Section_1_2_1.Part13
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


/-- The dyadic cube containing x at scale n indeed contains x. -/
lemma dyadicCubeContaining_mem {d:ℕ} (n:ℤ) (x : EuclideanSpace' d) :
    x ∈ (dyadicCubeContaining n x).toSet := by
  intro i
  simp only [dyadicCubeContaining, DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
  have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num : (0:ℝ) < 2) n
  constructor
  · have h1 : (⌊x i * 2^n⌋ : ℝ) ≤ x i * 2^n := Int.floor_le _
    calc (⌊x i * 2^n⌋ : ℝ) / 2^n ≤ x i * 2^n / 2^n := div_le_div_of_nonneg_right h1 (le_of_lt h2n_pos)
      _ = x i := by field_simp
  · have h2 : x i * 2^n < ⌊x i * 2^n⌋ + 1 := Int.lt_floor_add_one _
    have h3 : x i < ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n := by
      calc x i = x i * 2^n / 2^n := by field_simp
        _ < (⌊x i * 2^n⌋ + 1) / 2^n := div_lt_div_of_pos_right h2 h2n_pos
        _ = ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n := by ring
    exact h3.le

/-- The interior of a dyadic cube is nonempty. -/
lemma dyadicCubeInteriorNonempty {d:ℕ} (n:ℤ) (a: Fin d → ℤ) :
    (interior (s := (DyadicCube n a).toSet)).Nonempty := by
  rw [Box.interior_toSet]
  exact (Set.univ_pi_nonempty_iff.mpr (fun k => by
    simp only [DyadicCube, BoundedInterval.toSet, interior_Icc]
    exact Set.nonempty_Ioo.mpr (div_lt_div_of_pos_right (by linarith) (zpow_pos (by norm_num) _))
  )).preimage (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).surjective

lemma Box.toSet_nonempty_of_IsDyadic {d : ℕ} {B : Box d} (hB : B.IsDyadic) : B.toSet.Nonempty := by
  obtain ⟨n, ⟨a, rfl⟩⟩ := hB
  exact (dyadicCubeInteriorNonempty n a).mono (interior_subset (s := (DyadicCube n a).toSet))

/-- At the same scale, dyadic cubes with different indices cannot have one contained in the other
    (since containment would imply empty interior for one). -/
lemma dyadicCubeNoProperContainmentSameScale {d:ℕ} {n:ℤ} {a b : Fin d → ℤ}
    (h_sub : (DyadicCube n a).toSet ⊆ (DyadicCube n b).toSet) : a = b := by
  by_contra hne
  have h_ad := DyadicCube.almost_disjoint_same_scale (n := n) (a := a) (b := b) hne
  simp only [AlmostDisjoint] at h_ad
  have h_int_sub : interior (s := (DyadicCube n a).toSet) ⊆ interior (s := (DyadicCube n b).toSet) :=
    interior_mono h_sub
  have h_int_eq : interior (s := (DyadicCube n a).toSet) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hx' := h_int_sub hx
    have hx_both : x ∈ interior (s := (DyadicCube n a).toSet) ∩
        interior (s := (DyadicCube n b).toSet) := ⟨hx, hx'⟩
    rw [h_ad] at hx_both
    exact hx_both
  exact Set.not_nonempty_empty (h_int_eq ▸ dyadicCubeInteriorNonempty n a)

/-- A larger dyadic cube (coarser scale n) cannot be contained in a smaller dyadic cube (finer scale m)
    when d > 0. This is because the sidelength 2^(-n) > 2^(-m) when n < m. -/
lemma dyadicCubeLargerNotInSmaller {d:ℕ} (hd : 0 < d) {n m : ℤ} (hnm : n < m)
    {a b : Fin d → ℤ} : ¬((DyadicCube n a).toSet ⊆ (DyadicCube m b).toSet) := by
  intro h_sub
  -- Pick any coordinate (d > 0 guarantees this exists)
  let i : Fin d := ⟨0, hd⟩
  -- Compare sidelengths: 2^(-n) > 2^(-m) when n < m
  have h_side_ineq : (2:ℝ)^(-m) < (2:ℝ)^(-n) := by
    apply zpow_lt_zpow_right₀ (by norm_num : 1 < (2:ℝ))
    omega
  -- Construct the left endpoint of DyadicCube n a
  let x_left : EuclideanSpace' d := .toLp 2 (fun j => (a j : ℝ) / 2^n)
  -- x_left is in DyadicCube n a (it's the left corner)
  have hx_left : x_left ∈ (DyadicCube n a).toSet := by
    intro j
    simp only [x_left, DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
    constructor
    · exact le_refl _
    · have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num) n
      apply le_of_lt
      apply div_lt_div_of_pos_right _ h2n_pos
      linarith
  -- Construct the right endpoint of DyadicCube n a
  let x_right : EuclideanSpace' d := .toLp 2 (fun j => ((a j : ℝ) + 1) / 2^n)
  -- x_right is in DyadicCube n a (it's the right corner)
  have hx_right : x_right ∈ (DyadicCube n a).toSet := by
    intro j
    simp only [x_right, DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
    constructor
    · have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num) n
      apply le_of_lt
      apply div_lt_div_of_pos_right _ h2n_pos
      linarith
    · exact le_refl _
  -- Both endpoints are in DyadicCube m b by h_sub
  have h_left_in := h_sub hx_left i
  have h_right_in := h_sub hx_right i
  simp only [x_left, x_right, DyadicCube, BoundedInterval.toSet, Set.mem_Icc] at h_left_in h_right_in
  -- From h_left_in: (a i)/2^n ≥ (b i)/2^m
  -- From h_right_in: ((a i)+1)/2^n ≤ ((b i)+1)/2^m
  -- So: 2^(-n) = ((a i)+1)/2^n - (a i)/2^n ≤ ((b i)+1)/2^m - (b i)/2^m = 2^(-m)
  have h_len_sub : (2:ℝ)^(-n) ≤ (2:ℝ)^(-m) := by
    have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num) n
    have h2m_pos : (0:ℝ) < 2^m := zpow_pos (by norm_num) m
    calc (2:ℝ)^(-n) = ((a i : ℝ) + 1) / 2^n - (a i : ℝ) / 2^n := by
            simp only [zpow_neg, ← sub_div]; norm_cast; simp [add_sub_cancel_left]
      _ ≤ ((b i : ℝ) + 1) / 2^m - (b i : ℝ) / 2^m := by linarith [h_left_in.1, h_right_in.2]
      _ = (2:ℝ)^(-m) := by
            simp only [zpow_neg, ← sub_div]; norm_cast; simp [add_sub_cancel_left]
  linarith

/-- Lemma 1.2.11: Every open set is a countable union of almost disjoint dyadic cubes.
Note: every dyadic cube is nonempty
    Proof outline:
    1. For each x ∈ E, by {name}`IsOpen.exists_dyadic_cube_subset`, there exists a dyadic cube containing x ⊆ E
    2. The set of all such dyadic cubes is countable (subset of {lean}`ℕ × (Fin d → ℤ)`)
    3. Take maximal cubes (not strictly contained in another cube in the collection)
    4. By {name}`DyadicCube.nesting`, distinct maximal cubes are almost disjoint
    5. E equals the union of these maximal cubes -/
theorem IsOpen.eq_union_boxes {d:ℕ} (hd : 0 < d) (E: Set (EuclideanSpace' d)) (hE: IsOpen E)
    (hE_nonempty : E.Nonempty) :
    ∃ B: ℕ → Box d, (E = ⋃ n, (B n).toSet) ∧ (∀ n, (B n).IsDyadic) ∧
    Pairwise (Function.onFun AlmostDisjoint B) := by
  classical
  -- Construct maximal dyadic cubes
  obtain ⟨x₀, hx₀⟩ := hE_nonempty
  -- Define the set of all dyadic cubes (at scale n ≥ 0) contained in E
  let Q : Set (ℕ × (Fin d → ℤ)) := { p | (DyadicCube (p.1 : ℤ) p.2).toSet ⊆ E }
  -- Q is countable as a subset of ℕ × (Fin d → ℤ)
  have hQ_countable : Q.Countable := Set.countable_of_injective_of_countable_image
    (f := id) (fun _ _ _ _ h => h) (Set.countable_univ.mono (Set.subset_univ _))
  -- For each x ∈ E, find the minimal scale n such that the dyadic cube at scale n containing x is in Q
  -- Minimal scale corresponds to maximal cube (smaller n = coarser = larger cubes)
  have h_exists_min_scale : ∀ x ∈ E, ∃ n₀ : ℕ, ∃ a : Fin d → ℤ,
      x ∈ (DyadicCube (n₀:ℤ) a).toSet ∧ (DyadicCube (n₀:ℤ) a).toSet ⊆ E ∧
      (∀ m < n₀, ∀ b : Fin d → ℤ, x ∈ (DyadicCube (m:ℤ) b).toSet → ¬(DyadicCube (m:ℤ) b).toSet ⊆ E) := by
    intro x hx
    -- By exists_dyadic_cube_subset, there exists some scale with cube ⊆ E
    obtain ⟨n, a, hxa, hcube⟩ := hE.exists_dyadic_cube_subset hx
    -- Find the minimal such scale using Nat.find
    let P : ℕ → Prop := fun m => ∃ b : Fin d → ℤ, x ∈ (DyadicCube (m:ℤ) b).toSet ∧ (DyadicCube (m:ℤ) b).toSet ⊆ E
    have hP : ∃ m, P m := ⟨n, a, hxa, hcube⟩
    let n₀ := Nat.find hP
    obtain ⟨a₀, ha₀_mem, ha₀_sub⟩ := Nat.find_spec hP
    use n₀, a₀, ha₀_mem, ha₀_sub
    intro m hm b hb_mem hsub
    exact Nat.find_min hP hm ⟨b, hb_mem, hsub⟩
  -- Define maximal cubes: for each x ∈ E, pick the cube at minimal scale
  -- Define the set of maximal cube indices
  let Q_max : Set (ℕ × (Fin d → ℤ)) := { p | (DyadicCube (p.1 : ℤ) p.2).toSet ⊆ E ∧
    ∀ q : ℕ × (Fin d → ℤ), q.1 < p.1 →
      (DyadicCube (p.1 : ℤ) p.2).toSet ⊆ (DyadicCube (q.1 : ℤ) q.2).toSet →
      ¬(DyadicCube (q.1 : ℤ) q.2).toSet ⊆ E }
  -- Q_max is countable
  have hQ_max_countable : Q_max.Countable :=
    Set.countable_of_injective_of_countable_image (f := id) (fun _ _ _ _ h => h)
      (Set.countable_univ.mono (Set.subset_univ _))
  -- Q_max is nonempty (since E is nonempty)
  have hQ_max_nonempty : Q_max.Nonempty := by
    obtain ⟨n₀, a₀, hx₀_mem, hsub, hmin⟩ := h_exists_min_scale x₀ hx₀
    use ⟨n₀, a₀⟩
    simp only [Set.mem_setOf_eq, Q_max]
    constructor
    · exact hsub
    · intro q hq hsub'
      -- If DyadicCube n₀ a₀ ⊆ DyadicCube q.1 q.2 with q.1 < n₀, then q.1 is a smaller scale
      -- containing x₀, contradicting minimality
      have hx₀_in_q : x₀ ∈ (DyadicCube (q.1 : ℤ) q.2).toSet := hsub' hx₀_mem
      exact hmin q.1 hq q.2 hx₀_in_q
  -- Q_max is infinite: we show this by cases on d
  have hQ_max_infinite : Q_max.Infinite := by
    -- d > 0 by hypothesis hd, so we proceed directly
      -- At scale 0, dyadic cubes are [a₁, a₁+1] × ... × [aₐ, aₐ+1] for a ∈ ℤᵈ
      -- If E = univ, all scale-0 cubes are in Q_max
      -- If E ≠ univ, near the boundary, cubes at arbitrarily fine scales are maximal
      by_cases hE_univ : E = Set.univ
      · -- E = univ: All scale-0 cubes are maximal (no coarser scale exists)
        -- First, show Fin d → ℤ is infinite (since d > 0 and ℤ is infinite)
        haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
        haveI : Infinite (Fin d → ℤ) := Function.infinite_of_right
        -- Now inject Fin d → ℤ into Q_max via a ↦ (0, a)
        apply Set.infinite_of_injective_forall_mem
          (f := fun a : Fin d → ℤ => (0, a))
          (fun a b hab => (Prod.mk.inj hab).2)
        intro a
        constructor
        · simp only [hE_univ]; exact Set.subset_univ _
        · intro q hq _; omega
      · -- E ≠ univ: Near boundary, cubes at arbitrarily fine scales are maximal
        -- Key insight: Since E ≠ univ, there exists y ∉ E. For any x ∈ E, the maximal
        -- cube containing x cannot contain y. As we move x closer to y (within E),
        -- the maximal cubes must become smaller, giving arbitrarily fine scales.
        -- We show Q_max is infinite by showing the scales are unbounded.
        by_contra hfin
        rw [Set.not_infinite] at hfin
        -- Q_max is finite, so there's a maximum scale N among all maximal cubes
        obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ p ∈ Q_max, p.1 ≤ N := by
          obtain ⟨p, hp⟩ := Set.Finite.exists_maximalFor Prod.fst Q_max hfin hQ_max_nonempty
          use p.1
          intro q hq
          by_contra hlt
          push_neg at hlt
          have hle := hp.le_of_le hq hlt.le
          omega
        -- But there exist points in E whose maximal cube has scale > N
        -- These are points close to the boundary (complement of E)
        -- Since E ≠ univ, ∃ y ∉ E. Take x ∈ E close to y.
        have hEc_nonempty : Eᶜ.Nonempty := by
          rw [Set.nonempty_compl]
          exact hE_univ
        obtain ⟨y, hy⟩ := hEc_nonempty
        -- Proof strategy:
        -- 1. Every x ∈ E has a maximal cube with scale ≤ N, hence sidelength ≥ 2^(-N)
        -- 2. This cube is contained in E and contains an open ball around x
        -- 3. So every x ∈ E has dist(x, Eᶜ) ≥ 2^(-N)·sqrt(d)/2 (roughly)
        -- 4. This means E is closed (closure E = E)
        -- 5. E is open, closed, nonempty → E = univ by connectedness
        -- 6. Contradicts E ≠ univ
        --
        -- Step 1: Show E is closed
        have hE_closed : IsClosed E := by
          -- Strategy: Q_max is finite, so E is a finite union of dyadic cubes
          -- Each dyadic cube is closed (product of closed intervals Icc)
          -- Finite union of closed sets is closed
          -- First, show each dyadic cube toSet is closed
          have h_cube_closed : ∀ p ∈ Q_max, IsClosed (DyadicCube (p.1 : ℤ) p.2).toSet := by
            intro p _
            -- DyadicCube is product of Icc intervals, which are closed
            exact Box.isClosed_toSet_of_Icc _ (fun i => ⟨_, _, rfl⟩)
          -- E equals the union of cubes in Q_max
          have hE_union_Qmax : E = ⋃ p ∈ Q_max, (DyadicCube (p.1 : ℤ) p.2).toSet := by
            ext x
            constructor
            · intro hx
              -- x ∈ E, so x has a maximal cube
              obtain ⟨n₀, a₀, hx_mem, hsub, hmin⟩ := h_exists_min_scale x hx
              -- This cube is in Q_max
              have h_in_Qmax : (n₀, a₀) ∈ Q_max := by
                constructor
                · exact hsub
                · intro q hq hsub'
                  have : x ∈ (DyadicCube (q.1 : ℤ) q.2).toSet := hsub' hx_mem
                  exact hmin q.1 hq q.2 this
              exact Set.mem_biUnion h_in_Qmax hx_mem
            · intro hx
              simp only [Set.mem_iUnion] at hx
              obtain ⟨p, hp_mem, hx_in_p⟩ := hx
              exact hp_mem.1 hx_in_p
          -- Q_max is finite, so the union is finite
          rw [hE_union_Qmax]
          -- Finite union of closed sets is closed
          exact hfin.isClosed_biUnion h_cube_closed
        -- Step 2: E is clopen (closed and open)
        have hE_clopen : IsClopen E := ⟨hE_closed, hE⟩
        -- Step 3: Use preconnectedness
        -- EuclideanSpace d is preconnected for d > 0
        haveI : PreconnectedSpace (EuclideanSpace' d) := inferInstance
        -- Step 4: Clopen sets in preconnected space are either empty or univ
        rw [isClopen_iff] at hE_clopen
        cases hE_clopen with
        | inl h_empty =>
          -- E = ∅ contradicts E.Nonempty
          have : E.Nonempty := ⟨x₀, hx₀⟩
          rw [h_empty] at this
          exact Set.not_nonempty_empty this
        | inr h_univ =>
          -- E = univ contradicts hE_univ : E ≠ univ
          exact hE_univ h_univ
  -- Enumerate Q_max using the Denumerable structure (since Q_max is infinite and countable)
  obtain ⟨p₀, hp₀⟩ := hQ_max_nonempty
  -- For infinite countable sets, we can get an injective enumeration
  haveI : Infinite Q_max := Set.infinite_coe_iff.mpr hQ_max_infinite
  haveI : Countable Q_max := hQ_max_countable.to_subtype
  haveI : Denumerable Q_max := Denumerable.ofEncodableOfInfinite Q_max
  -- Use the denumerable equiv to get a bijection
  let B_enum : ℕ ≃ Q_max := (Denumerable.eqv Q_max).symm
  let B_idx : ℕ → ℕ × (Fin d → ℤ) := fun n => (B_enum n).val
  have hB_idx_inj : Function.Injective B_idx := by
    intro i j hij
    have : B_enum i = B_enum j := Subtype.ext hij
    exact (Equiv.injective B_enum) this
  let B : ℕ → Box d := fun n => DyadicCube ((B_idx n).1 : ℤ) (B_idx n).2
  use B
  constructor
  · -- E = ⋃ n, (B n).toSet
    ext x
    constructor
    · -- x ∈ E → x ∈ ⋃ n, (B n).toSet
      intro hx
      obtain ⟨n₀, a₀, hxa₀, hsub, hmin⟩ := h_exists_min_scale x hx
      -- (n₀, a₀) ∈ Q_max
      have h_in_Qmax : (⟨n₀, a₀⟩ : ℕ × (Fin d → ℤ)) ∈ Q_max := by
        simp only [Set.mem_setOf_eq, Q_max]
        constructor
        · exact hsub
        · intro q hq hsub'
          have hx_in_q : x ∈ (DyadicCube (q.1 : ℤ) q.2).toSet := hsub' hxa₀
          exact hmin q.1 hq q.2 hx_in_q
      -- B_enum is a bijection ℕ ≃ Q_max, so (n₀, a₀) ∈ Q_max has a preimage
      rw [Set.mem_iUnion]
      -- h_in_Qmax : (n₀, a₀) ∈ Q_max, and B_enum is surjective
      let elem : Q_max := ⟨(n₀, a₀), h_in_Qmax⟩
      have h_in_range : elem ∈ Set.range B_enum := by
        rw [Equiv.range_eq_univ]
        exact Set.mem_univ _
      obtain ⟨k, hk⟩ := h_in_range
      use k
      show x ∈ (DyadicCube ((B_idx k).1 : ℤ) (B_idx k).2).toSet
      have heq : B_idx k = (n₀, a₀) := by
        simp only [B_idx]
        exact congrArg Subtype.val hk
      rw [heq]
      exact hxa₀
    · -- x ∈ ⋃ n, (B n).toSet → x ∈ E
      intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨n, hn⟩ := hx
      have h_Bn_mem : B_idx n ∈ Q_max := (B_enum n).property
      exact h_Bn_mem.1 hn
  constructor
  · -- ∀ n, (B n).IsDyadic
    intro n
    simp only [B, Box.IsDyadic]
    use (B_idx n).1, (B_idx n).2
  · -- Pairwise almost disjoint
    intro i j hij
    simp only [Function.onFun]
    have hi_mem : B_idx i ∈ Q_max := (B_enum i).property
    have hj_mem : B_idx j ∈ Q_max := (B_enum j).property
    -- Two distinct maximal cubes are almost disjoint
    -- By DyadicCube.nesting: either almost disjoint, or one ⊆ other
    rcases DyadicCube.nesting (n := (B_idx i).1) (m := (B_idx j).1)
        (a := (B_idx i).2) (b := (B_idx j).2) with h_ad | h_ij | h_ji
    · exact h_ad
    · -- B i ⊆ B j: analyze by scale comparison
      exfalso
      -- h_ij : (DyadicCube (B_idx i).1 (B_idx i).2).toSet ⊆ (DyadicCube (B_idx j).1 (B_idx j).2).toSet
      -- If B_i ⊆ B_j strictly, then (B_idx j).1 < (B_idx i).1 (j is coarser)
      -- By maximality of B_i, since B_i ⊆ B_j and j.1 < i.1, we have B_j ⊈ E
      -- But B_j ∈ Q_max implies B_j ⊆ E. Contradiction.
      rcases lt_trichotomy (B_idx j).1 (B_idx i).1 with hji_lt | hji_eq | hji_gt
      · -- (B_idx j).1 < (B_idx i).1: j is coarser scale
        -- B_i ⊆ B_j and j.1 < i.1 contradicts maximality of B_i
        exact hi_mem.2 (B_idx j) hji_lt h_ij hj_mem.1
      · -- Same scale: cubes are either equal or disjoint
        -- If B_i ⊆ B_j at same scale, they must be equal
        have h_ij' : (DyadicCube (↑(B_idx i).1) (B_idx i).2).toSet ⊆
            (DyadicCube (↑(B_idx i).1) (B_idx j).2).toSet := by
          convert h_ij using 3; simp only [Nat.cast_inj]; exact hji_eq.symm
        have heq : (B_idx i).2 = (B_idx j).2 := dyadicCubeNoProperContainmentSameScale h_ij'
        -- If scales and indices equal, B_i = B_j, so B_idx i = B_idx j
        have hidx_eq : B_idx i = B_idx j := Prod.ext hji_eq.symm (funext fun x => congrFun heq x)
        -- By injectivity of B_idx (from Denumerable enumeration), i = j
        exact hij (hB_idx_inj hidx_eq)
      · -- (B_idx i).1 < (B_idx j).1: i is coarser scale (larger cube), j is finer (smaller cube)
        -- h_ij says larger cube ⊆ smaller cube, geometrically impossible for d > 0
        have h_scale_lt : (↑(B_idx i).1 : ℤ) < ↑(B_idx j).1 := by exact_mod_cast hji_gt
        exact dyadicCubeLargerNotInSmaller hd h_scale_lt h_ij
    · -- B j ⊆ B i: symmetric case
      exfalso
      rcases lt_trichotomy (B_idx i).1 (B_idx j).1 with hij_lt | hij_eq | hij_gt
      · -- i coarser (larger), j finer (smaller), B_j ⊆ B_i is geometrically valid
        -- This contradicts maximality of B_j: B_j ⊆ B_i ⊆ E, and i is coarser
        exact hj_mem.2 (B_idx i) hij_lt h_ji hi_mem.1
      · -- Same scale: use injectivity as in the symmetric case above
        have h_ji' : (DyadicCube (↑(B_idx j).1) (B_idx j).2).toSet ⊆
            (DyadicCube (↑(B_idx j).1) (B_idx i).2).toSet := by
          convert h_ji using 3; simp only [Nat.cast_inj]; exact hij_eq.symm
        have heq : (B_idx j).2 = (B_idx i).2 := dyadicCubeNoProperContainmentSameScale h_ji'
        have hidx_eq : B_idx j = B_idx i := Prod.ext hij_eq.symm (funext fun x => congrFun heq x)
        exact hij (hB_idx_inj hidx_eq).symm
      · -- j coarser (larger), i finer (smaller), B_j ⊆ B_i means larger inside smaller
        -- Geometric impossibility for d > 0
        have h_scale_lt : (↑(B_idx j).1 : ℤ) < ↑(B_idx i).1 := by exact_mod_cast hij_gt
        exact dyadicCubeLargerNotInSmaller hd h_scale_lt h_ji

theorem Lebesgue_outer_measure.of_open {d:ℕ} (E: Set (EuclideanSpace' d)) (hE: IsOpen E) : Lebesgue_outer_measure E = Jordan_inner_measure' E := by
  by_cases hd : d = 0
  · -- Dimension 0: In dim 0, open sets are either ∅ or Set.univ
    subst hd
    -- every set is bounded in dimension zero, so the extended inner measure is the usual one
    rw [Jordan_inner_measure'_eq_coe (EuclideanSpace'.isBounded_of_dim_zero E),
      Lebesgue_outer_measure_of_dim_zero]
    by_cases hne : E.Nonempty
    · -- Case: E is nonempty → E = Set.univ in dimension 0
      simp only [hne, ↓reduceIte]
      -- Show Jordan_inner_measure E = 1
      -- E = Set.univ since EuclideanSpace' 0 is singleton and E is nonempty
      have hE_univ : E = Set.univ := by
        ext x
        constructor
        · intro _; exact Set.mem_univ x
        · intro _
          obtain ⟨y, hy⟩ := hne
          have : x = y := by ext i; exact i.elim0
          rw [this]; exact hy
      -- Set.univ is elementary with measure 1 in dimension 0
      let B : Box 0 := ⟨fun i => i.elim0⟩
      have hB_univ : B.toSet = Set.univ := by
        ext x; simp only [Box.toSet, Set.mem_univ, iff_true]; intro i; exact i.elim0
      have hB_vol : |B|ᵥ = 1 := by simp only [Box.volume, Finset.univ_eq_empty, Finset.prod_empty]
      -- Jordan_inner_measure E ≥ measure of B (since B ⊆ E = univ)
      have h_ge : (IsElementary.box B).measure ≤ Jordan_inner_measure E := by
        unfold Jordan_inner_measure
        apply le_csSup
        · use 1
          intro m hm
          obtain ⟨A, hA, hA_subset, rfl⟩ := hm
          -- Any elementary subset of Set.univ in dim 0 has measure ≤ 1
          by_cases hA_ne : A.Nonempty
          · have hA_univ : A = Set.univ := by
              ext x; constructor; intro _; exact Set.mem_univ x
              intro _; obtain ⟨y, hy⟩ := hA_ne; have : x = y := by ext i; exact i.elim0
              rw [this]; exact hy
            have : hA.measure = 1 := by
              have h_eq : hA.measure = (IsElementary.box B).measure := by
                apply IsElementary.measure_eq_of_set_eq; rw [hA_univ, hB_univ]
              rw [h_eq, IsElementary.measure_of_box, hB_vol]
            rw [this]
          · have hA_empty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA_ne
            have : hA.measure = 0 := by
              have h_eq : hA.measure = (IsElementary.empty 0).measure :=
                IsElementary.measure_eq_of_set_eq hA (IsElementary.empty 0) hA_empty
              rw [h_eq, IsElementary.measure_of_empty]
            rw [this]; norm_num
        · use B.toSet, IsElementary.box B; simp [hE_univ, hB_univ]
      -- Jordan_inner_measure E ≤ 1 (since E ⊆ Set.univ and univ has outer measure 1)
      have h_le : Jordan_inner_measure E ≤ 1 := by
        unfold Jordan_inner_measure
        apply csSup_le
        · use 0, ∅, IsElementary.empty 0; simp [IsElementary.measure_of_empty]
        · intro m hm
          obtain ⟨A, hA, hA_subset, rfl⟩ := hm
          by_cases hA_ne : A.Nonempty
          · have hA_univ : A = Set.univ := by
              ext x; constructor; intro _; exact Set.mem_univ x
              intro _; obtain ⟨y, hy⟩ := hA_ne; have : x = y := by ext i; exact i.elim0
              rw [this]; exact hy
            have : hA.measure = 1 := by
              have h_eq : hA.measure = (IsElementary.box B).measure := by
                apply IsElementary.measure_eq_of_set_eq; rw [hA_univ, hB_univ]
              rw [h_eq, IsElementary.measure_of_box, hB_vol]
            rw [this]
          · have hA_empty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA_ne
            have : hA.measure = 0 := by
              have h_eq : hA.measure = (IsElementary.empty 0).measure :=
                IsElementary.measure_eq_of_set_eq hA (IsElementary.empty 0) hA_empty
              rw [h_eq, IsElementary.measure_of_empty]
            rw [this]; norm_num
      -- Combine h_ge and h_le to get Jordan_inner_measure E = 1
      have h_jordan_eq_1 : Jordan_inner_measure E = 1 := by
        rw [IsElementary.measure_of_box, hB_vol] at h_ge
        exact (h_ge.antisymm h_le).symm
      rw [h_jordan_eq_1]
      norm_num
    · -- Case: E is empty
      have hE_empty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp only [hne, if_false]
      subst hE_empty
      -- Show (0 : EReal) = ↑(Jordan_inner_measure ∅)
      -- First prove Jordan_inner_measure ∅ = 0
      have h_jordan_empty : Jordan_inner_measure (∅ : Set (EuclideanSpace' 0)) = 0 := by
        unfold Jordan_inner_measure
        apply le_antisymm
        · apply csSup_le
          · use 0, ∅, IsElementary.empty 0; simp [IsElementary.measure_of_empty]
          · intro m hm
            obtain ⟨A, hA, hA_subset, rfl⟩ := hm
            have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
            subst hA_empty
            exact le_of_eq (IsElementary.measure_of_empty 0)
        · apply le_csSup
          · use 0; intro m hm
            obtain ⟨A, hA, hA_subset, rfl⟩ := hm
            have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
            subst hA_empty
            exact le_of_eq (IsElementary.measure_of_empty 0)
          · use ∅, IsElementary.empty 0; simp [IsElementary.measure_of_empty]
      rw [h_jordan_empty]
      norm_num
  · push_neg at hd
    have hd' : 0 < d := Nat.pos_of_ne_zero hd
    by_cases hE_empty : E = ∅
    · -- Empty set case: use Lebesgue_outer_measure.of_empty and Jordan_inner_measure ∅ = 0
      subst hE_empty
      rw [Jordan_inner_measure'_eq_coe Bornology.isBounded_empty,
        Lebesgue_outer_measure.of_empty]
      -- Show (0 : EReal) = ↑(Jordan_inner_measure ∅)
      -- First prove Jordan_inner_measure ∅ = 0
      have h_jordan_empty : Jordan_inner_measure (∅ : Set (EuclideanSpace' d)) = 0 := by
        unfold Jordan_inner_measure
        apply le_antisymm
        · apply csSup_le
          · use 0, ∅, IsElementary.empty d; simp [IsElementary.measure_of_empty]
          · intro m hm
            obtain ⟨A, hA, hA_subset, rfl⟩ := hm
            have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
            subst hA_empty
            exact le_of_eq (IsElementary.measure_of_empty d)
        · apply le_csSup
          · use 0; intro m hm
            obtain ⟨A, hA, hA_subset, rfl⟩ := hm
            have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
            subst hA_empty
            exact le_of_eq (IsElementary.measure_of_empty d)
          · use ∅, IsElementary.empty d; simp [IsElementary.measure_of_empty]
      rw [h_jordan_empty]
      norm_num
    · -- Main case: E nonempty open set in dimension > 0
      have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
      -- Decompose E into almost-disjoint dyadic boxes
      obtain ⟨B, hE_eq, hB_dyadic, hB_disj⟩ := IsOpen.eq_union_boxes hd' E hE hE_nonempty
      -- Apply lemma eq_Jordan_inner_of_boxes (Exercise 1.2.5)
      exact Lebesgue_outer_measure.eq_Jordan_inner_of_boxes E B hE_eq hB_disj

/-- Lemma 1.2.12 (Outer regularity). m\*(E) = inf\{m\*(U) : E ⊆ U, U open\}. -/
theorem Lebesgue_outer_measure.eq {d:ℕ} (E: Set (EuclideanSpace' d)) : Lebesgue_outer_measure E = sInf { M | ∃ U, E ⊆ U ∧ IsOpen U ∧ M = Lebesgue_outer_measure U} := by
  let S := { M | ∃ U, E ⊆ U ∧ IsOpen U ∧ M = Lebesgue_outer_measure U}
  apply le_antisymm
  · -- ≤ direction: m*(E) ≤ sInf S (by monotonicity, m*(E) is a lower bound)
    apply le_csInf
    · -- S is nonempty (Set.univ is open and contains E)
      exact ⟨Lebesgue_outer_measure Set.univ, Set.univ, Set.subset_univ E, isOpen_univ, rfl⟩
    · -- m*(E) is a lower bound for S
      intro M ⟨U, hE_sub_U, _hU_open, hM_eq⟩
      rw [hM_eq]
      exact Lebesgue_outer_measure.mono hE_sub_U
  · -- ≥ direction: sInf S ≤ m*(E) (main work)
    -- Handle dimension 0 separately
    by_cases hd : d = 0
    · -- d = 0: In dimension 0, EuclideanSpace' 0 is a singleton type
      subst hd
      have h_singleton : ∀ (y z : EuclideanSpace' 0), y = z := fun y z =>
        PiLp.ext fun i => Fin.elim0 i
      by_cases hE_empty : E = ∅
      · -- E = ∅: m*(∅) = 0, and sInf S ≥ 0 (all outer measures are ≥ 0)
        -- Actually we need sInf S ≤ m*(E) = 0
        -- Since ∅ is open and contains E = ∅, m*(∅) ∈ S
        rw [hE_empty]
        apply csInf_le_of_le
        · use 0
          intro M ⟨U, _, _, hM⟩
          rw [hM]
          exact Lebesgue_outer_measure.nonneg U
        · exact ⟨∅, Set.Subset.rfl, isOpen_empty, rfl⟩
        · exact le_refl _
      · -- E ≠ ∅: Then E = Set.univ (since every nonempty set in a singleton is univ)
        have hE_univ : E = Set.univ := by
          ext x; constructor
          · intro _; exact Set.mem_univ x
          · intro _
            have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
            obtain ⟨e, he⟩ := hE_nonempty
            rw [h_singleton x e]
            exact he
        rw [hE_univ]
        apply csInf_le_of_le
        · use 0
          intro M ⟨U, _, _, hM⟩
          rw [hM]
          exact Lebesgue_outer_measure.nonneg U
        · exact ⟨Set.univ, Set.subset_univ _, isOpen_univ, rfl⟩
        · exact le_refl _
    -- d > 0: main argument
    push_neg at hd
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    -- Case split on whether m*(E) = ⊤
    by_cases h_top : Lebesgue_outer_measure E = ⊤
    · -- m*(E) = ⊤: trivially sInf S ≤ ⊤
      rw [h_top]
      exact le_top
    -- m*(E) is finite: use ε-argument
    apply EReal.le_of_forall_pos_le_add'
    intro ε hε
    -- Use ε/2 for the cover and ε/2 for the inflation to get total bound m*(E) + ε
    have hε2_pos : 0 < ε / 2 := by linarith
    -- Get cover close to m*(E): ∃ B₁, B₂,... with ∑|Bₙ| ≤ m*(E) + ε/2
    obtain ⟨B, hB_cover, hB_sum⟩ := exists_cover_close hd_pos E (ε/2) hε2_pos h_top
    -- Inflate each box Bₙ to open box B'ₙ with |B'ₙ| ≤ |Bₙ| + (ε/2)/2^{n+1}
    have h_inflate : ∀ n, ∃ B'n : Box d, (B n).toSet ⊆ interior B'n.toSet ∧
        IsOpen (interior B'n.toSet) ∧ |B'n|ᵥ ≤ |(B n)|ᵥ + (ε/2) / 2^(n+1) := by
      intro n
      have h_eps_pos : 0 < (ε/2) / 2^(n+1) := by positivity
      exact Box.inflate (B n) ((ε/2) / 2^(n+1)) h_eps_pos
    choose B' hB'_subset hB'_open hB'_vol using h_inflate
    -- Define the open set U = ⋃ₙ interior B'ₙ
    let U := ⋃ n, interior (B' n).toSet
    -- U is open (union of open sets)
    have hU_open : IsOpen U := isOpen_iUnion (fun n => hB'_open n)
    -- E ⊆ U (since E ⊆ ⋃ₙ Bₙ.toSet ⊆ ⋃ₙ interior B'ₙ.toSet = U)
    have hE_sub_U : E ⊆ U := fun x hx => by
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hB_cover hx)
      exact Set.mem_iUnion.mpr ⟨n, hB'_subset n hn⟩
    -- m*(U) ≤ ∑ₙ m*(interior B'ₙ.toSet) ≤ ∑ₙ |B'ₙ|ᵥ (by subadditivity + elementary measure)
    have hU_measure : Lebesgue_outer_measure U ≤ ∑' n, (B' n).volume.toEReal := by
      -- First: m*(U) ≤ ∑' m*(interior B'ₙ) by countable subadditivity
      have h_subadditive := Lebesgue_outer_measure.union_le (fun n => interior (B' n).toSet)
      -- Second: ∀n, m*(interior B'ₙ) ≤ |B'ₙ|ᵥ
      have h_pointwise : ∀ n, Lebesgue_outer_measure (interior (B' n).toSet) ≤ (B' n).volume.toEReal := by
        intro n
        calc Lebesgue_outer_measure (interior (B' n).toSet)
            ≤ Lebesgue_outer_measure (B' n).toSet := Lebesgue_outer_measure.mono interior_subset
          _ = (B' n).volume.toEReal := by
              have h_elem : IsElementary (B' n).toSet := IsElementary.box (B' n)
              rw [Lebesgue_outer_measure.elementary (B' n).toSet h_elem, IsElementary.measure_of_box]
      -- Third: use EReal tsum comparison
      have h_nonneg_f : ∀ n, 0 ≤ Lebesgue_outer_measure (interior (B' n).toSet) :=
        fun n => Lebesgue_outer_measure.nonneg _
      have h_nonneg_g : ∀ n, 0 ≤ (B' n).volume := fun n => Box.volume_nonneg _
      have h_summable_g : Summable (fun n => (B' n).volume) := by
        -- |B'ₙ| ≤ |Bₙ| + (ε/2)/2^{n+1}. Summable because:
        -- 1. Geometric series ∑(ε/2)/2^{n+1} is summable
        -- 2. B-volumes sum to ≤ m*(E) + ε/2 < ⊤, so they are summable in ℝ
        -- 3. By comparison test, B'-volumes are summable
        -- Technical details deferred to summability lemmas
        have h_geom_summable : Summable (fun n : ℕ => ε / 2 / 2 ^ (n + 1)) := by
          -- Use tsum_geometric_eps pattern: ∑ ε/2^{n+1} = ε
          -- So ∑ (ε/2)/2^{n+1} = ε/2, which converges
          have h_summable_base : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
            summable_geometric_of_lt_one (by norm_num) (by norm_num)
          have h_eq : (fun n : ℕ => ε / 2 / 2 ^ (n + 1)) = (fun n : ℕ => (ε / 4) * (1/2)^n) := by
            ext n
            have h_two_pow_pos : (0 : ℝ) < 2^(n+1) := by positivity
            have h_two_pow_ne : (2 : ℝ)^(n+1) ≠ 0 := h_two_pow_pos.ne'
            field_simp [h_two_pow_ne]
            ring_nf; simp
          rw [h_eq]
          exact h_summable_base.mul_left (ε / 4)
        have h_B_nonneg : ∀ n, 0 ≤ (B n).volume := fun n => Box.volume_nonneg _
        have h_B_summable : Summable (fun n => (B n).volume) := by
          -- From hB_sum: ∑' (B n).volume.toEReal ≤ m*(E) + ε/2 < ⊤
          -- Extract a real upper bound from hB_sum
          have h_rhs_ne_top : Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≠ ⊤ :=
            EReal.add_ne_top h_top (EReal.coe_ne_top _)
          -- Get a real bound M such that the tsum ≤ M
          have h_exists_M : ∃ M : ℝ, Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≤ M := by
            cases h_rhs : (Lebesgue_outer_measure E + (↑(ε / 2) : EReal)) with
            | bot => exact ⟨0, le_of_lt (EReal.bot_lt_coe _)⟩
            | coe r => exact ⟨r, le_refl _⟩
            | top => exact (h_rhs_ne_top h_rhs).elim
          obtain ⟨M, hM_ge⟩ := h_exists_M
          have h_tsum_le_M : ∑' n, (B n).volume.toEReal ≤ M := le_trans hB_sum hM_ge
          -- Use summable_of_sum_range_le: need ∀ n, ∑_{i<n} f i ≤ M
          apply summable_of_sum_range_le h_B_nonneg
          intro n
          have h_partial := EReal.finset_sum_le_tsum h_B_nonneg (Finset.range n)
          have h_chain := le_trans h_partial h_tsum_le_M
          rw [← EReal.coe_finset_sum (fun i _ => h_B_nonneg i)] at h_chain
          exact EReal.coe_le_coe_iff.mp h_chain
        exact Summable.of_nonneg_of_le (fun n => Box.volume_nonneg _)
          (fun n => hB'_vol n) (h_B_summable.add h_geom_summable)
      calc Lebesgue_outer_measure U
          ≤ ∑' n, Lebesgue_outer_measure (interior (B' n).toSet) := h_subadditive
        _ ≤ ∑' n, (B' n).volume.toEReal :=
            EReal.tsum_le_coe_tsum_of_forall_le h_nonneg_f h_nonneg_g h_summable_g h_pointwise
    -- ∑ₙ |B'ₙ|ᵥ ≤ ∑ₙ (|Bₙ|ᵥ + (ε/2)/2^{n+1}) = ∑ₙ |Bₙ|ᵥ + ε/2 (since ∑(ε/2)/2^{n+1} = ε/2)
    have hB'_vol_sum : (∑' n, (B' n).volume.toEReal) ≤ (∑' n, (B n).volume.toEReal) + (ε/2 : ℝ) := by
      -- Pointwise: |B'ₙ| ≤ |Bₙ| + (ε/2)/2^{n+1}
      -- So ∑|B'ₙ| ≤ ∑|Bₙ| + ∑(ε/2)/2^{n+1} = ∑|Bₙ| + ε/2
      have h_B_nonneg : ∀ n, 0 ≤ (B n).volume := fun n => Box.volume_nonneg _
      have h_geom_nonneg : ∀ n, 0 ≤ (ε/2) / 2^(n+1) := fun n => by positivity
      have h_pw : ∀ n, (B n).volume + (ε/2) / 2^(n+1) ≤ (B n).volume + (ε/2) / 2^(n+1) := fun n => le_refl _
      -- Use helper: ∑|B'ₙ| ≤ ∑(|Bₙ| + δₙ) since |B'ₙ| ≤ |Bₙ| + δₙ
      have h_B'_le_sum : ∀ n, (B' n).volume ≤ (B n).volume + (ε/2) / 2^(n+1) := hB'_vol
      have h_B'_nonneg : ∀ n, 0 ≤ (B' n).volume := fun n => Box.volume_nonneg _
      have h_B'_nonneg_EReal : ∀ n, (0 : EReal) ≤ (B' n).volume.toEReal :=
        fun n => EReal.coe_nonneg.mpr (h_B'_nonneg n)
      -- ∑|B'ₙ| ≤ ∑(|Bₙ| + δₙ) by pointwise bound
      have h_step1 : (∑' n, (B' n).volume.toEReal) ≤ ∑' n, ((B n).volume + (ε/2) / 2^(n+1)).toEReal := by
        apply EReal.tsum_le_coe_tsum_of_forall_le h_B'_nonneg_EReal
          (fun n => add_nonneg (h_B_nonneg n) (h_geom_nonneg n))
        · -- Summability of |Bₙ| + δₙ
          have h_geom_summable : Summable (fun n : ℕ => (ε/2) / 2^(n+1)) := by
            have h_summable_base : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
              summable_geometric_of_lt_one (by norm_num) (by norm_num)
            have h_eq : (fun n : ℕ => (ε/2) / 2 ^ (n + 1)) = (fun n : ℕ => (ε / 4) * (1/2)^n) := by
              ext n
              have h_two_pow_ne : (2 : ℝ)^(n+1) ≠ 0 := by positivity
              field_simp [h_two_pow_ne]; ring_nf; simp
            rw [h_eq]
            exact h_summable_base.mul_left (ε / 4)
          have h_B_summable : Summable (fun n => (B n).volume) := by
            have h_rhs_ne_top : Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≠ ⊤ :=
              EReal.add_ne_top h_top (EReal.coe_ne_top _)
            have h_exists_M : ∃ M : ℝ, Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≤ M := by
              cases h_rhs : (Lebesgue_outer_measure E + (↑(ε / 2) : EReal)) with
              | bot => exact ⟨0, le_of_lt (EReal.bot_lt_coe _)⟩
              | coe r => exact ⟨r, le_refl _⟩
              | top => exact (h_rhs_ne_top h_rhs).elim
            obtain ⟨M, hM_ge⟩ := h_exists_M
            have h_tsum_le_M : ∑' n, (B n).volume.toEReal ≤ M := le_trans hB_sum hM_ge
            apply summable_of_sum_range_le h_B_nonneg
            intro n
            have h_partial := EReal.finset_sum_le_tsum h_B_nonneg (Finset.range n)
            have h_chain := le_trans h_partial h_tsum_le_M
            rw [← EReal.coe_finset_sum (fun i _ => h_B_nonneg i)] at h_chain
            exact EReal.coe_le_coe_iff.mp h_chain
          exact h_B_summable.add h_geom_summable
        · exact fun n => EReal.coe_le_coe_iff.mpr (h_B'_le_sum n)
      -- Now split ∑(|Bₙ| + δₙ) = ∑|Bₙ| + ∑δₙ
      have h_step2 : (∑' n, ((B n).volume + (ε/2) / 2^(n+1)).toEReal) =
          (∑' n, (B n).volume.toEReal) + (∑' n, ((ε/2) / 2^(n+1)).toEReal) := by
        -- For Real, we have ∑(f + g) = ∑f + ∑g when summable
        have h_geom_summable : Summable (fun n : ℕ => (ε/2) / 2^(n+1)) := by
          have h_summable_base : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
            summable_geometric_of_lt_one (by norm_num) (by norm_num)
          have h_eq : (fun n : ℕ => (ε/2) / 2 ^ (n + 1)) = (fun n : ℕ => (ε / 4) * (1/2)^n) := by
            ext n
            have h_two_pow_ne : (2 : ℝ)^(n+1) ≠ 0 := by positivity
            field_simp [h_two_pow_ne]; ring_nf; simp
          rw [h_eq]
          exact h_summable_base.mul_left (ε / 4)
        have h_B_summable : Summable (fun n => (B n).volume) := by
          have h_rhs_ne_top : Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≠ ⊤ :=
            EReal.add_ne_top h_top (EReal.coe_ne_top _)
          have h_exists_M : ∃ M : ℝ, Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≤ M := by
            cases h_rhs : (Lebesgue_outer_measure E + (↑(ε / 2) : EReal)) with
            | bot => exact ⟨0, le_of_lt (EReal.bot_lt_coe _)⟩
            | coe r => exact ⟨r, le_refl _⟩
            | top => exact (h_rhs_ne_top h_rhs).elim
          obtain ⟨M, hM_ge⟩ := h_exists_M
          have h_tsum_le_M : ∑' n, (B n).volume.toEReal ≤ M := le_trans hB_sum hM_ge
          apply summable_of_sum_range_le h_B_nonneg
          intro n
          have h_partial := EReal.finset_sum_le_tsum h_B_nonneg (Finset.range n)
          have h_chain := le_trans h_partial h_tsum_le_M
          rw [← EReal.coe_finset_sum (fun i _ => h_B_nonneg i)] at h_chain
          exact EReal.coe_le_coe_iff.mp h_chain
        -- Use tsum_add for Real
        have h_real_tsum : ∑' n, ((B n).volume + (ε/2) / 2^(n+1)) =
            (∑' n, (B n).volume) + (∑' n, (ε/2) / 2^(n+1)) :=
          h_B_summable.tsum_add h_geom_summable
        -- Convert to EReal
        have h_sum_nonneg : ∀ n, 0 ≤ (B n).volume + (ε/2) / 2^(n+1) :=
          fun n => add_nonneg (h_B_nonneg n) (h_geom_nonneg n)
        -- Use symm to get: ∑' ↑(...) = ↑(∑' ...)
        rw [← EReal.coe_tsum_of_nonneg h_sum_nonneg (h_B_summable.add h_geom_summable)]
        rw [← EReal.coe_tsum_of_nonneg h_B_nonneg h_B_summable]
        rw [← EReal.coe_tsum_of_nonneg h_geom_nonneg h_geom_summable]
        rw [h_real_tsum]
        simp only [EReal.coe_add]
      -- ∑δₙ = ε/2
      have h_geom_sum : (∑' n, ((ε/2) / 2^(n+1)).toEReal) = (ε/2 : EReal) := by
        -- ∑ (ε/2)/2^{n+1} = (ε/2) * ∑ 1/2^{n+1} = (ε/2) * 1 = ε/2
        have h_geom_summable' : Summable (fun n : ℕ => (ε/2) / 2^(n+1)) := by
          have h_summable_base : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
            summable_geometric_of_lt_one (by norm_num) (by norm_num)
          have h_eq : (fun n : ℕ => (ε/2) / 2 ^ (n + 1)) = (fun n : ℕ => (ε / 4) * (1/2)^n) := by
            ext n
            have h_two_pow_ne : (2 : ℝ)^(n+1) ≠ 0 := by positivity
            field_simp [h_two_pow_ne]; ring_nf; simp
          rw [h_eq]
          exact h_summable_base.mul_left (ε / 4)
        have h_real_sum : ∑' n : ℕ, (ε/2) / 2^(n+1) = ε/2 := by
          have h_eq : (fun n : ℕ => (ε/2) / 2^(n+1)) = (fun n : ℕ => (ε/2) * (1/2)^(n+1)) := by
            ext n; field_simp; simp
          rw [h_eq, tsum_mul_left]
          have h_geom_sum_one : ∑' n : ℕ, (1/2 : ℝ)^(n+1) = 1 := by
            have h_summable : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
              summable_geometric_of_lt_one (by norm_num) (by norm_num)
            have h_formula := h_summable.sum_add_tsum_nat_add 1
            simp only [Finset.range_one, Finset.sum_singleton, pow_zero] at h_formula
            rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1)] at h_formula
            linarith
          rw [h_geom_sum_one]; ring
        -- Convert EReal tsum: ∑' n, (ε/2 / 2^(n+1)).toEReal = (ε/2 : EReal)
        rw [← EReal.coe_tsum_of_nonneg h_geom_nonneg h_geom_summable', h_real_sum, EReal.coe_div]
        norm_cast
      calc ∑' n, (B' n).volume.toEReal
          ≤ ∑' n, ((B n).volume + (ε/2) / 2^(n+1)).toEReal := h_step1
        _ = (∑' n, (B n).volume.toEReal) + (∑' n, ((ε/2) / 2^(n+1)).toEReal) := h_step2
        _ = (∑' n, (B n).volume.toEReal) + (ε/2 : EReal) := by rw [h_geom_sum]
    -- Combine: m*(U) ≤ m*(E) + ε
    have hU_bound : Lebesgue_outer_measure U ≤ Lebesgue_outer_measure E + ε := by
      calc Lebesgue_outer_measure U
          ≤ ∑' n, (B' n).volume.toEReal := hU_measure
        _ ≤ (∑' n, (B n).volume.toEReal) + (ε/2 : ℝ) := hB'_vol_sum
        _ ≤ (Lebesgue_outer_measure E + (ε/2 : ℝ)) + (ε/2 : ℝ) := by
            apply add_le_add_left hB_sum
        _ = Lebesgue_outer_measure E + ε := by
            rw [add_assoc]
            congr 1
            norm_cast
            ring
    -- sInf S ≤ m*(U) since U ∈ S
    have h_U_in_S : Lebesgue_outer_measure U ∈ S :=
      ⟨U, hE_sub_U, hU_open, rfl⟩
    calc sInf S
        ≤ Lebesgue_outer_measure U := csInf_le ⟨0, fun M ⟨V, _, _, hM⟩ => hM ▸ Lebesgue_outer_measure.nonneg V⟩ h_U_in_S
      _ ≤ Lebesgue_outer_measure E + ε := hU_bound

/-- For any set E and ε > 0, there exists an open U ⊇ E with m*(U) ≤ m*(E) + ε.
    This follows from outer regularity (Lemma 1.2.12). -/
lemma Lebesgue_outer_measure.exists_open_superset_measure_le {d:ℕ} (E: Set (EuclideanSpace' d)) (ε : EReal) (hε : 0 < ε) :
    ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure U ≤ Lebesgue_outer_measure E + ε := by
  -- By outer regularity (Lebesgue_outer_measure.eq):
  -- m*(E) = sInf { m*(U) | E ⊆ U ∧ IsOpen U }
  have h_outer_reg := Lebesgue_outer_measure.eq (d := d) E
  let S := {M | ∃ U, E ⊆ U ∧ IsOpen U ∧ M = Lebesgue_outer_measure U}
  have h_set_nonempty : S.Nonempty := by
    use Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d))
    exact ⟨Set.univ, Set.subset_univ E, isOpen_univ, rfl⟩
  have h_inf : IsGLB S (sInf S) := isGLB_sInf S
  have h_ne_bot : sInf S ≠ ⊥ := by
    intro h_eq
    rw [h_eq] at h_inf
    have h_zero_lb : (0 : EReal) ∈ lowerBounds S := by
      intro v hv
      obtain ⟨U, _, _, rfl⟩ := hv
      exact Lebesgue_outer_measure.nonneg U
    have h_le : (0 : EReal) ≤ ⊥ := h_inf.2 h_zero_lb
    exact not_le.mpr EReal.bot_lt_zero h_le
  by_cases h_top : sInf S = ⊤
  · use Set.univ
    refine ⟨isOpen_univ, Set.subset_univ E, ?_⟩
    rw [h_outer_reg, h_top]
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact le_top
    | coe r => exact le_top
  · have h_lt : sInf S < sInf S + ε := by
      cases ε with
      | bot => exact absurd hε (not_lt.mpr bot_le)
      | top =>
        have h_sum_top : sInf S + ⊤ = ⊤ := by
          cases h : sInf S with
          | bot => exact absurd h h_ne_bot
          | top => exact absurd h h_top
          | coe r => rfl
        rw [h_sum_top]
        exact lt_top_iff_ne_top.mpr h_top
      | coe r =>
        have hr_pos : 0 < r := EReal.coe_pos.mp hε
        exact EReal.lt_add_of_pos_coe hr_pos h_ne_bot h_top
    have h_not_lb : sInf S + ε ∉ lowerBounds S := by
      intro h_is_lb
      have h_le : sInf S + ε ≤ sInf S := h_inf.2 h_is_lb
      exact not_lt.mpr h_le h_lt
    unfold lowerBounds at h_not_lb
    simp only [Set.mem_setOf_eq] at h_not_lb
    push_neg at h_not_lb
    obtain ⟨v, hv_in_S, hv_lt⟩ := h_not_lb
    obtain ⟨U, hE_sub_U, hU_open, hv_eq⟩ := hv_in_S
    use U
    refine ⟨hU_open, hE_sub_U, ?_⟩
    rw [h_outer_reg, ← hv_eq]
    exact le_of_lt hv_lt

/-- Compact sets in Euclidean space have finite Lebesgue outer measure. -/
lemma Lebesgue_outer_measure.finite_of_compact {d : ℕ} {E : Set (EuclideanSpace' d)}
    (hE : IsCompact E) : Lebesgue_outer_measure E ≠ ⊤ := by
  -- Empty case is trivial
  by_cases hE_empty : E = ∅
  · rw [hE_empty, Lebesgue_outer_measure.of_empty]; exact EReal.zero_ne_top
  -- For nonempty E: E compact → E bounded → E ⊆ closedBall x R → E ⊆ box [-M,M]^d
  have ⟨x, hx⟩ : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
  have h_bounded : Bornology.IsBounded E := IsCompact.isBounded hE
  have ⟨r, h_sub_ball⟩ : ∃ (r : ℝ), E ⊆ Metric.closedBall x r := by
    rwa [← Metric.isBounded_iff_subset_closedBall x]
  -- Create a large box B that contains the closed ball
  let M := ‖x‖ + |r| + 2
  let B : Box d := { side := fun _ => BoundedInterval.Icc (-M) M }
  have h_E_sub_B : E ⊆ B.toSet := by
    intro y hy
    have h_in_ball : y ∈ Metric.closedBall x r := h_sub_ball hy
    simp only [Box.mem_toSet]
    intro i
    rw [Metric.mem_closedBall] at h_in_ball
    have h_dist : ‖y - x‖ ≤ r := h_in_ball
    have h_coord_diff : |(y - x) i| ≤ ‖y - x‖ := EuclideanSpace'.coord_le_norm (y - x) i
    have h_abs : |y i - x i| ≤ r := le_trans h_coord_diff h_dist
    have h_xi : |x i| ≤ ‖x‖ := EuclideanSpace'.coord_le_norm x i
    show y i ∈ (BoundedInterval.Icc (-M) M : Set ℝ)
    rw [BoundedInterval.set_Icc, Set.mem_Icc]
    rw [abs_le] at h_abs h_xi
    have h_r_bound : r ≤ |r| := le_abs_self r
    constructor <;> linarith
  have : IsElementary B.toSet := IsElementary.box B
  have h_B_finite : Lebesgue_outer_measure B.toSet ≠ ⊤ := by
    rw [Lebesgue_outer_measure.elementary B.toSet this]
    exact EReal.coe_ne_top _
  exact ne_top_of_le_ne_top h_B_finite (Lebesgue_outer_measure.mono h_E_sub_B)

