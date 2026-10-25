import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Topology.Instances.Irrational
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2: Lebesgue measure

A companion to (the introduction to) Section 1.2 of the book "An introduction to Measure Theory".

-/


/-- Exercise 1.2.1 (countable union) -/
lemma exercise_1_2_1_union :
    ∃ E: ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
      (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n))) ∧
      (∀ n, E n ⊆ Set.Icc 0 1) ∧
      ¬ JordanMeasurable (⋃ n, Real.equiv_EuclideanSpace' '' (E n)) := by
  -- Strategy: Let E_n = {q_n} where q_n is the nth rational in [0,1]
  -- Each singleton is Jordan measurable with measure 0
  -- But the union is all rationals in [0,1], which is NOT Jordan measurable

  -- Get an enumeration of rationals in [0,1]
  have h_countable : (Set.Icc (0:ℚ) 1).Countable := Set.countable_coe_iff.mp inferInstance
  have h_nonempty : (Set.Icc (0:ℚ) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨q, hq_surj⟩ := h_countable.exists_surjective h_nonempty

  -- Define E_n = {q_n} (singleton containing the nth rational)
  let E : ℕ → Set ℝ := fun n => {((q n).val : ℝ)}

  use E

  constructor
  -- Part 1: Each E_n is bounded (singleton sets are trivially bounded)
  · intro n
    apply Set.Finite.isBounded
    exact Set.finite_singleton _

  constructor
  -- Part 2: Each E_n is Jordan measurable (singletons have measure 0)
  · intro n
    -- A singleton {x} in ℝ maps to a degenerate box in EuclideanSpace' 1
    -- Specifically, Real.equiv_EuclideanSpace' '' {x} = Icc x x (as a 1D box)
    -- Boxes are elementary, and elementary sets are Jordan measurable
    let x := ((q n).val : ℝ)
    have h_singleton_eq : Real.equiv_EuclideanSpace' '' {x} = (BoundedInterval.Icc x x : Box 1).toSet := by
      rw [BoundedInterval.coe_of_box]
      simp [BoundedInterval.set_Icc]
    rw [h_singleton_eq]
    exact IsElementary.jordanMeasurable (IsElementary.box _)

  constructor
  -- Part 3: Each E_n is contained in [0,1]
  · intro n x hx
    simp [E] at hx
    rcases hx with rfl
    rcases (q n).property with ⟨hq0, hq1⟩
    exact ⟨by exact_mod_cast hq0, by exact_mod_cast hq1⟩

  -- Part 4: The union ⋃_n E_n = rationals in [0,1], which is NOT Jordan measurable
  · intro hJM
    -- The union equals the set of all rationals in [0,1]
    have h_union_eq_rats : (⋃ n, E n) = Set.range (fun r : Set.Icc (0:ℚ) 1 => (r.val : ℝ)) := by
      ext x
      simp only [E, Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_range]
      constructor
      · intro ⟨n, hn⟩
        use q n
        exact hn.symm
      · intro ⟨r, hr⟩
        obtain ⟨n, hn⟩ := hq_surj r
        use n
        rw [hn]
        exact hr.symm

    -- The image of the union under Real.equiv_EuclideanSpace' is the image of rationals
    have hJM' : JordanMeasurable (Real.equiv_EuclideanSpace' '' (⋃ n, E n)) := by
      have : (⋃ n, Real.equiv_EuclideanSpace' '' E n) = Real.equiv_EuclideanSpace' '' (⋃ n, E n) := by
        exact Set.image_iUnion.symm
      rw [← this]
      exact hJM

    -- Let Q = rationals in [0,1]
    let Q := Set.range (fun r : Set.Icc (0:ℚ) 1 => (r.val : ℝ))

    -- Show Q is bounded
    have hQ_bounded : Bornology.IsBounded Q := by
      apply Bornology.IsBounded.subset (Metric.isBounded_Icc (a := 0) (b := 1))
      intro x hx
      obtain ⟨r, hr⟩ := hx
      rw [← hr]
      simp
      have : r.val ∈ Set.Icc (0:ℚ) 1 := r.property
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2

    -- Rewrite hJM' in terms of Q
    rw [h_union_eq_rats] at hJM'

    -- Use Exercise 1.1.18(1): Jordan_outer_measure(closure(Q)) = Jordan_outer_measure(Q)
    have h_outer_eq : Jordan_outer_measure (closure (Real.equiv_EuclideanSpace' '' Q)) =
                      Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Q) := by
      apply JordanMeasurable.outer_measure_of_closure
      have : Bornology.IsBounded (Real.equiv_EuclideanSpace' '' Q) := by
        -- Q ⊆ [0,1] is bounded, so its image under the homeomorphism is bounded
        -- Use that Q is bounded: ∃ M, ∀ x y ∈ Q, dist x y ≤ M
        obtain ⟨c, hc⟩ := Metric.isBounded_iff_subset_ball 0 |>.mp hQ_bounded
        -- Show image is bounded by showing it's in a ball
        rw [Metric.isBounded_iff_subset_ball 0]
        use c
        intro v hv
        obtain ⟨x, hx, rfl⟩ := hv
        -- Show Real.equiv_EuclideanSpace' x ∈ Metric.ball 0 c
        -- Since ‖Real.equiv_EuclideanSpace' x‖ = |x| and x ∈ Metric.ball 0 c
        have hx_ball : x ∈ Metric.ball 0 c := hc hx
        rw [Metric.mem_ball, dist_zero_right] at hx_ball
        rw [Metric.mem_ball, dist_zero_right]
        -- ‖Real.equiv_EuclideanSpace' x‖ = |x|
        have h_norm_eq : ‖Real.equiv_EuclideanSpace' x‖ = |x| := by
          simp [Real.equiv_EuclideanSpace', EuclideanSpace'.equiv_Real]
          rw [PiLp.norm_eq_of_L2]
          simp
          exact Real.sqrt_sq_eq_abs x
        rw [h_norm_eq]
        exact hx_ball
      exact this

    -- Closure of rationals in [0,1] is [0,1] (rationals are dense)
    have h_closure_Q : closure Q = Set.Icc 0 1 := by
      -- Rationals are dense in [0,1]
      -- First show Q ⊆ [0,1]
      have hQ_subset : Q ⊆ Set.Icc 0 1 := by
        intro y hy
        simp [Q] at hy
        obtain ⟨r, ⟨h_bounds, h_eq⟩⟩ := hy
        rw [← h_eq]
        constructor
        · exact_mod_cast h_bounds.1
        · exact_mod_cast h_bounds.2
      -- Show closure Q ⊆ [0,1] (since [0,1] is closed)
      have h_closure_subset : closure Q ⊆ Set.Icc 0 1 :=
        closure_minimal hQ_subset isClosed_Icc
      -- Show [0,1] ⊆ closure Q (using density of rationals)
      have h_subset_closure : Set.Icc 0 1 ⊆ closure Q := by
        -- Q is the set of rationals in [0,1]
        -- Since rationals are dense in ℝ, Q is dense in [0,1]
        -- Therefore closure Q ⊇ [0,1]
        intro x hx
        -- Use DenseRange for rationals
        have h_dense : ∀ ε > 0, ∃ q : ℚ, |(q:ℝ) - x| < ε ∧ (q:ℝ) ∈ Set.Icc 0 1 := by
          intro ε hε
          -- Find a rational within ε of x using density
          have := Rat.denseRange_cast.exists_dist_lt x hε
          obtain ⟨q, hq⟩ := this
          -- Check if q ∈ [0,1]
          by_cases hq_in : (q:ℝ) ∈ Set.Icc 0 1
          · use q
            have : |(q:ℝ) - x| < ε := by
              rw [← Real.dist_eq, dist_comm]
              exact hq
            exact ⟨this, hq_in⟩
          · -- If q ∉ [0,1], need to find a rational in [0,1] close to x
            -- Recursively use density in a smaller neighborhood that stays within [0,1]
            -- Define the interval [a, b] = [max(0, x-ε/2), min(1, x+ε/2)] ⊆ [0,1]
            let a := max (0 : ℝ) (x - ε / 2)
            let b := min (1 : ℝ) (x + ε / 2)
            have ha : 0 ≤ a := le_max_left _ _
            have hb : b ≤ 1 := min_le_left _ _
            have hax : a ≤ x := by
              simp only [a]
              exact max_le (hx.1) (by linarith)
            have hxb : x ≤ b := by
              simp only [b]
              exact le_min (hx.2) (by linarith)
            have hab : a < b := by
              simp only [a, b]
              apply max_lt
              · -- 0 < min 1 (x + ε / 2)
                apply lt_min
                · norm_num
                · linarith [hx.1, hε]
              · apply lt_min
                · linarith [hx.2]
                · linarith
            -- Find a rational in the open interval (a, b) using density
            have : ∃ r : ℚ, a < (r : ℝ) ∧ (r : ℝ) < b := by
              apply exists_rat_btwn
              exact hab
            obtain ⟨r, har, hrb⟩ := this
            use r
            constructor
            · -- |r - x| < ε
              have : (r : ℝ) ∈ Set.Ioo a b := ⟨har, hrb⟩
              simp [a, b] at this
              rw [abs_sub_lt_iff]
              constructor <;> linarith
            · -- r ∈ [0, 1]
              rw [Set.mem_Icc]
              constructor <;> linarith [har, ha, hrb, hb]
        -- Use h_dense to show x ∈ closure Q
        apply Metric.mem_closure_iff.mpr
        intro ε hε
        obtain ⟨q, hq_dist, hq_in⟩ := h_dense ε hε
        use (q:ℝ)
        constructor
        · -- Show (q:ℝ) ∈ Q (first subgoal from "use")
          simp only [Q, Set.mem_range]
          have hq_bounds : q ∈ Set.Icc (0:ℚ) 1 := by
            rw [Set.mem_Icc] at hq_in ⊢
            exact ⟨by exact_mod_cast hq_in.1, by exact_mod_cast hq_in.2⟩
          use ⟨q, hq_bounds⟩
        · -- Show dist (q:ℝ) x < ε (second subgoal from "use")
          rw [Real.dist_eq]
          rw [abs_sub_comm] at hq_dist
          exact hq_dist
      exact Set.Subset.antisymm h_closure_subset h_subset_closure

    -- Use Real.equiv_EuclideanSpace' commutes with closure
    have h_image_closure : Real.equiv_EuclideanSpace' '' closure Q =
                           closure (Real.equiv_EuclideanSpace' '' Q) := by
      -- Real.equiv_EuclideanSpace' is a homeomorphism (continuous bijection with continuous inverse)
      -- Homeomorphisms preserve closure: f(closure A) = closure(f(A))
      -- To prove this formally would require:
      -- 1. Showing Real.equiv_EuclideanSpace' is continuous (it's the coordinate embedding x ↦ (fun _ => x))
      -- 2. Showing its inverse is continuous (it's the projection (f : Fin 1 → ℝ) ↦ f 0)
      -- 3. Applying image_closure_subset_closure_image in both directions
      -- These are all true but require detailed work with the topology API
      classical
      -- Continuity of the forward and inverse maps
      have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
        show Continuous (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
        exact continuous_induced_rng.mpr (continuous_pi (fun _ => continuous_id))
      have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
        exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) ⟨0, by decide⟩
      -- Package the equivalence as a homeomorphism to apply the library lemma
      let e : ℝ ≃ₜ EuclideanSpace' 1 :=
        { toEquiv := Real.equiv_EuclideanSpace'
          continuous_toFun := hf_cont
          continuous_invFun := hg_cont }
      have h := e.image_closure Q
      have he : (⇑e : ℝ → EuclideanSpace' 1) = Real.equiv_EuclideanSpace' := by
        rw [← e.coe_toEquiv]
      simpa [he] using h

    rw [← h_image_closure] at h_outer_eq
    rw [h_closure_Q] at h_outer_eq

    -- [0,1] is a 1D box with Jordan outer measure 1
    have h_Icc_outer : Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Set.Icc 0 1) = 1 := by
      -- [0,1] maps to a 1D box [0,1] which is elementary with measure 1
      -- First show that the image is a box
      have h_eq_box : Real.equiv_EuclideanSpace' '' Set.Icc 0 1 = (BoundedInterval.Icc 0 1 : Box 1).toSet := by
        rw [BoundedInterval.coe_of_box]
        simp [BoundedInterval.set_Icc]
      rw [h_eq_box]
      -- This is an elementary set (a box)
      let B := (BoundedInterval.Icc 0 1 : Box 1)
      have hB_elem : IsElementary B.toSet := IsElementary.box B
      -- For an elementary set, Jordan_outer_measure = its measure
      have h_outer_eq_measure : Jordan_outer_measure B.toSet = hB_elem.measure := by
        -- Jordan_outer_measure B = sInf { m | ∃ A elementary, B ⊆ A ∧ m = hA.measure }
        -- Since B is elementary and B ⊆ B, we have hB_elem.measure in the set
        -- Need to show: sInf of this set = hB_elem.measure
        apply le_antisymm
        · -- Jordan_outer_measure B ≤ hB_elem.measure
          exact Jordan_outer_le hB_elem (Set.Subset.refl B.toSet)
        · -- hB_elem.measure ≤ Jordan_outer_measure B
          -- For any A elementary with B ⊆ A, we have hB_elem.measure ≤ hA.measure
          unfold Jordan_outer_measure
          apply le_csInf
          · -- Show the set is nonempty
            use hB_elem.measure, B.toSet, hB_elem, Set.Subset.refl B.toSet
          · -- Show hB_elem.measure is a lower bound
            intro m hm
            obtain ⟨A, hA, hB_subset_A, rfl⟩ := hm
            exact IsElementary.measure_mono hB_elem hA hB_subset_A
      rw [h_outer_eq_measure]
      -- The measure of the box [0,1] is 1
      have h_measure_eq_volume : hB_elem.measure = |B|ᵥ := IsElementary.measure_of_box B
      rw [h_measure_eq_volume]
      -- Volume of 1D box is the length of its side
      simp [Box.volume, B, BoundedInterval.length]

    -- So Q has outer measure 1
    rw [h_Icc_outer] at h_outer_eq
    have h_Q_outer : Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Q) = 1 := h_outer_eq.symm

    -- Use Exercise 1.1.18(2): Jordan_inner_measure(interior(Q)) = Jordan_inner_measure(Q)
    have h_inner_eq : Jordan_inner_measure (interior (Real.equiv_EuclideanSpace' '' Q)) =
                      Jordan_inner_measure (Real.equiv_EuclideanSpace' '' Q) := by
      apply JordanMeasurable.inner_measure_of_interior
      have : Bornology.IsBounded (Real.equiv_EuclideanSpace' '' Q) := by
        -- Same proof as for outer measure
        obtain ⟨c, hc⟩ := Metric.isBounded_iff_subset_ball 0 |>.mp hQ_bounded
        rw [Metric.isBounded_iff_subset_ball 0]
        use c
        intro v hv
        obtain ⟨x, hx, rfl⟩ := hv
        have hx_ball : x ∈ Metric.ball 0 c := hc hx
        rw [Metric.mem_ball, dist_zero_right] at hx_ball
        rw [Metric.mem_ball, dist_zero_right]
        have h_norm_eq : ‖Real.equiv_EuclideanSpace' x‖ = |x| := by
          simp [Real.equiv_EuclideanSpace', EuclideanSpace'.equiv_Real]
          rw [PiLp.norm_eq_of_L2]
          simp
          exact Real.sqrt_sq_eq_abs x
        rw [h_norm_eq]
        exact hx_ball
      exact this

    -- Interior of Q (rationals) is empty (rationals have no interior)
    have h_interior_Q : interior Q = ∅ := by
      -- Rationals have empty interior because irrationals are dense
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      -- x ∈ interior Q means there's an open neighborhood of x contained in Q
      rw [mem_interior_iff_mem_nhds] at hx
      -- This means Q ∈ nhds x, which means there's an open set U with x ∈ U ⊆ Q
      obtain ⟨U, hU_Q, hU_open, hx_U⟩ := mem_nhds_iff.mp hx
      -- Find an open ball around x contained in U
      obtain ⟨ε, hε, hball_subset⟩ := Metric.isOpen_iff.mp hU_open x hx_U
      -- Use density of irrationals to find an irrational in the ball
      have h_ball_nonempty : (Metric.ball x ε).Nonempty := ⟨x, Metric.mem_ball_self hε⟩
      obtain ⟨y, hy_mem⟩ := Dense.inter_open_nonempty dense_irrational (Metric.ball x ε) Metric.isOpen_ball h_ball_nonempty
      rw [Set.mem_inter_iff] at hy_mem
      -- Components: first is y ∈ {x | Irrational x}, second is y ∈ Metric.ball x ε
      -- But Lean gives them in opposite order
      obtain ⟨hy_ball_mem, hy_irrat_mem⟩ := hy_mem
      -- y is in U (since ball ⊆ U)
      have hy_U : y ∈ U := hball_subset hy_ball_mem
      -- So y ∈ Q (since U ⊆ Q)
      have hy_Q : y ∈ Q := hU_Q hy_U
      -- But Q contains only rationals
      simp only [Q, Set.mem_range] at hy_Q
      obtain ⟨r, hr⟩ := hy_Q
      -- So y is rational: hr shows (r.val : ℝ) = y, so r.val is the rational witness
      have hy_rational : ∃ q : ℚ, (q:ℝ) = y := ⟨r.val, hr⟩
      -- But y is irrational: hy_irrat_mem : y ∈ {x | Irrational x}
      -- This means Irrational y, which contradicts hy_rational
      simp only [Set.mem_setOf_eq] at hy_irrat_mem
      exact hy_irrat_mem hy_rational

    -- Real.equiv_EuclideanSpace' commutes with interior
    have h_image_interior : Real.equiv_EuclideanSpace' '' interior Q =
                             interior (Real.equiv_EuclideanSpace' '' Q) := by
      -- This is a standard fact about homeomorphisms: they preserve interior
      -- The proof requires showing that Real.equiv_EuclideanSpace' and its inverse
      -- are both open maps (they map open sets to open sets)
      -- This is true because Real.equiv_EuclideanSpace' is a homeomorphism
      -- between ℝ and EuclideanSpace' 1
      classical
      -- Continuity of the forward and inverse maps
      have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
        show Continuous (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
        exact continuous_induced_rng.mpr (continuous_pi (fun _ => continuous_id))
      have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
        exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) ⟨0, by decide⟩
      -- Package these maps as a homeomorphism and apply the general lemma on interiors
      let e : ℝ ≃ₜ EuclideanSpace' 1 :=
        { toEquiv := Real.equiv_EuclideanSpace'
          continuous_toFun := hf_cont
          continuous_invFun := hg_cont }
      have h := e.image_interior Q
      have he : (⇑e : ℝ → EuclideanSpace' 1) = Real.equiv_EuclideanSpace' := by
        rw [← e.coe_toEquiv]
      simpa [he] using h

    rw [← h_image_interior] at h_inner_eq
    rw [h_interior_Q, Set.image_empty] at h_inner_eq

    -- Inner measure of empty set is 0
    have h_empty_inner : Jordan_inner_measure (∅ : Set (EuclideanSpace' 1)) = 0 := by
      -- The only elementary subset of ∅ is ∅, which has measure 0
      unfold Jordan_inner_measure
      -- Jordan_inner_measure ∅ = sSup { m | ∃ A elementary, A ⊆ ∅ ∧ m = hA.measure }
      -- The only A with A ⊆ ∅ is A = ∅, which has measure 0
      -- So the set is (at most) {0}, and sSup {0} = 0
      apply le_antisymm
      · -- sSup ≤ 0: show every element in the set is ≤ 0
        apply csSup_le
        · -- Show the set is nonempty
          use 0, ∅, IsElementary.empty 1
          simp [IsElementary.measure_of_empty]
        · -- Show every element is ≤ 0
          intro m hm
          obtain ⟨A, hA, hA_subset, rfl⟩ := hm
          -- A ⊆ ∅ means A = ∅
          have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
          -- So hA.measure = (IsElementary.empty 1).measure = 0
          subst hA_empty
          exact le_of_eq (IsElementary.measure_of_empty 1)
      · -- 0 ≤ sSup: 0 is in the set
        apply le_csSup
        · -- Show the set is bounded above
          use 0
          intro m hm
          obtain ⟨A, hA, hA_subset, rfl⟩ := hm
          have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
          subst hA_empty
          exact le_of_eq (IsElementary.measure_of_empty 1)
        · -- Show 0 is in the set
          use ∅, IsElementary.empty 1
          simp [IsElementary.measure_of_empty]

    rw [h_empty_inner] at h_inner_eq
    have h_Q_inner : Jordan_inner_measure (Real.equiv_EuclideanSpace' '' Q) = 0 := h_inner_eq.symm

    -- But Jordan measurable means inner = outer
    have h_eq : Jordan_inner_measure (Real.equiv_EuclideanSpace' '' Q) =
                Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Q) := by
      exact hJM'.2

    -- This gives 0 = 1, contradiction
    rw [h_Q_inner, h_Q_outer] at h_eq
    exact absurd h_eq (by norm_num)

-- The Jordan outer measure equals the infimum of sums of box volumes over all finite box covers.
theorem Jordan_outer_eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Jordan_outer_measure E = sInf (((fun S: Finset (Box d) ↦ ∑ B ∈ S, |B|ᵥ)) '' { S | E ⊆ ⋃ B ∈ S, B.toSet }) := by
  -- Strategy: Show equality via two inequalities (le_antisymm)
  apply le_antisymm

  -- Part 1 (≤): Jordan_outer_measure E ≤ sInf of box covers
  · -- For any box cover S, show Jordan_outer_measure E ≤ S.sum volume, then take infimum
    apply le_csInf
    -- Show the set of box cover sums is nonempty
    · obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
      obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
      use ∑ B ∈ T, |B|ᵥ
      use T
      simp
      intro a ha
      have : a ∈ A := hE_sub_A ha
      rw [hA_eq] at this
      exact this
    -- Show Jordan_outer_measure E is a lower bound for all box cover sums
    · intro m hm
      obtain ⟨S, hS_cover, rfl⟩ := hm
      -- The union ⋃ B ∈ S is elementary
      classical
      -- Map S : Finset (Box d) to a finset of sets
      let S_sets : Finset (Set (EuclideanSpace' d)) := S.image (fun B => B.toSet)
      have hS_elem : ∀ E ∈ S_sets, IsElementary E := by
        intro E hE
        simp [S_sets] at hE
        obtain ⟨B, _, rfl⟩ := hE
        exact IsElementary.box B
      -- Apply IsElementary.union' to show the union is elementary
      have h_union_eq : ⋃ E ∈ S_sets, E = ⋃ B ∈ S, B.toSet := by simp [S_sets]
      have hA_elem : IsElementary (⋃ B ∈ S, B.toSet) := by
        rw [←h_union_eq]
        exact IsElementary.union' hS_elem
      -- E ⊆ ⋃ B ∈ S, so Jordan_outer_measure E ≤ hA_elem.measure
      have h_outer_le : Jordan_outer_measure E ≤ hA_elem.measure := by
        unfold Jordan_outer_measure
        apply csInf_le
        · use 0; intro m' hm'; obtain ⟨_, hB, _, rfl⟩ := hm'; exact IsElementary.measure_nonneg hB
        · use ⋃ B ∈ S, B.toSet, hA_elem, hS_cover
      -- hA_elem.measure ≤ ∑ B ∈ S, |B|ᵥ by subadditivity (IsElementary.measure_of_union')
      have h_sub : hA_elem.measure ≤ ∑ B ∈ S, |B|ᵥ := by
        -- Apply IsElementary.measure_of_union' to get subadditivity
        have h1 := IsElementary.measure_of_union' hS_elem
        -- Show hA_elem.measure = (IsElementary.union' hS_elem).measure
        have h_eq : hA_elem.measure = (IsElementary.union' hS_elem).measure := by
          apply IsElementary.measure_eq_of_set_eq
          exact h_union_eq.symm
        -- Convert the sum over S_sets to sum over S
        -- Technical lemma: sum reindexing via Finset.sum_attach and Finset.sum_image
        have h2 : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ B ∈ S, |B|ᵥ := by
          -- Define a helper function to detach measure from proof
          let vol (E : Set (EuclideanSpace' d)) := if h : IsElementary E then h.measure else 0

          -- 1. Show RHS equals sum over S'
          let S' := S.filter (fun B => B.toSet.Nonempty)
          have h_rhs : ∑ B ∈ S, |B|ᵥ = ∑ B ∈ S', |B|ᵥ := by
             rw [←Finset.sum_filter_add_sum_filter_not S (fun B => B.toSet.Nonempty) (fun B => |B|ᵥ)]
             suffices ∑ B ∈ S.filter (fun B => ¬B.toSet.Nonempty), |B|ᵥ = 0 by simp [this, S']
             apply Finset.sum_eq_zero
             intro B hB
             rw [Finset.mem_filter] at hB
             exact Box.volume_eq_zero_of_empty B (Set.not_nonempty_iff_eq_empty.mp hB.2)
          rw [h_rhs]

          -- 2. Simplify LHS to use vol and sum over sets
          have h_lhs : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ E ∈ S_sets, vol E := by
            -- Congruence to vol
            have h_congr : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ E : S_sets, vol E.val := by
              apply Finset.sum_congr rfl
              intro E _
              dsimp [vol]
              rw [dif_pos (hS_elem E.val E.property)]
            rw [h_congr]
            -- Subtype sum to set sum
            change ∑ E ∈ S_sets.attach, vol E.val = ∑ E ∈ S_sets, vol E
            rw [Finset.sum_attach S_sets]
          rw [h_lhs]

          -- 3. Restrict set sum to non-empty sets
          let S_sets' := S'.image Box.toSet
          have h_subset : S_sets' ⊆ S_sets := Finset.image_subset_image (Finset.filter_subset _ _)

          have h_sets_eq : ∑ E ∈ S_sets, vol E = ∑ E ∈ S_sets', vol E := by
             rw [←Finset.sum_sdiff h_subset]
             suffices ∑ E ∈ S_sets \ S_sets', vol E = 0 by simp [this]
             apply Finset.sum_eq_zero
             intro E hE
             rw [Finset.mem_sdiff] at hE
             have hE_empty : E = ∅ := by
               obtain ⟨h_in, h_notin⟩ := hE
               rw [Finset.mem_image] at h_in
               obtain ⟨B, hB, rfl⟩ := h_in
               by_contra h_non
               apply h_notin
               simp [S_sets', S']
               use B
               simp [hB]
               rw [Set.nonempty_iff_ne_empty]
               exact h_non
             dsimp [vol]
             rw [hE_empty]
             rw [dif_pos (IsElementary.empty d)]
             exact IsElementary.measure_of_empty d
          rw [h_sets_eq]

          -- 4. Use sum_image
          rw [Finset.sum_image]
          · -- Match terms
            apply Finset.sum_congr rfl
            intro B hB
            dsimp [vol]
            rw [dif_pos (IsElementary.box B)]
            exact IsElementary.measure_of_box B
          · -- Injectivity
            intro B₁ hB₁ B₂ hB₂ h_eq
            simp [S'] at hB₁ hB₂
            -- Use helper lemma: Box.toSet is injective for non-empty boxes
            exact Box.toSet_injective_of_nonempty hB₁.2 hB₂.2 h_eq
        calc hA_elem.measure
          _ = (IsElementary.union' hS_elem).measure := h_eq
          _ ≤ ∑ E : S_sets, (hS_elem E.val E.property).measure := h1
          _ = ∑ B ∈ S, |B|ᵥ := h2
      linarith

  -- Part 2 (≥): sInf of box covers ≤ Jordan_outer_measure E
  · -- For any elementary A ⊇ E, show sInf(box covers) ≤ hA.measure
    unfold Jordan_outer_measure
    apply le_csInf
    -- Show the set of elementary cover measures is nonempty
    · obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
      use hA.measure
      use A, hA, hE_sub_A
    -- Show sInf(box covers) is a lower bound for all elementary cover measures
    · intro m hm
      obtain ⟨A, hA, hE_sub_A, rfl⟩ := hm
      -- Get partition T of A
      obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
      -- T is a box cover: E ⊆ A = ⋃ B ∈ T
      have hT_cover : E ⊆ ⋃ B ∈ T, B.toSet := hA_eq ▸ hE_sub_A
      -- T.sum volume = hA.measure
      have hT_sum : ∑ B ∈ T, |B|ᵥ = hA.measure := by
        symm; exact hA.measure_eq hT_disj hA_eq
      -- sInf(box covers) ≤ ∑ B ∈ T, |B|ᵥ (since T is a box cover)
      have h_inf_le : sInf (((fun S: Finset (Box d) ↦ ∑ B ∈ S, |B|ᵥ)) '' { S | E ⊆ ⋃ B ∈ S, B.toSet }) ≤ ∑ B ∈ T, |B|ᵥ := by
        apply csInf_le
        -- Show box covers set is bounded below
        · use 0
          intro m' hm'
          obtain ⟨S, _, rfl⟩ := hm'
          apply Finset.sum_nonneg
          intro B _
          rw [Box.volume]
          apply Finset.prod_nonneg
          intro i _
          rw [BoundedInterval.length]
          exact le_max_right _ _
        -- ∑ B ∈ T, |B|ᵥ is in the box covers set
        · show ∑ B ∈ T, |B|ᵥ ∈ (fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet}
          simp
          exact ⟨T, hT_cover, rfl⟩
      -- Combine: sInf(box covers) ≤ ∑ B ∈ T, |B|ᵥ = hA.measure
      rw [←hT_sum]; exact h_inf_le

