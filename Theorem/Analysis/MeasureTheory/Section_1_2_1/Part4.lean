import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Def.Analysis.MeasureTheory.Section_1_2_1.Part3
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


namespace Box

/-- The volume of a subdivided box equals the sum of its sub-box volumes -/
lemma volume_subdivide {d:ℕ} (B: Box d) :
    ∑ B' ∈ B.subdivide, |B'|ᵥ = |B|ᵥ := by
  unfold subdivide Box.volume
  -- Establish that each coordinate's length splits into two halves
  have h_sum : ∀ i, |(B.side i)|ₗ = |(B.side i).bisect.fst|ₗ + |(B.side i).bisect.snd|ₗ := by
    intro i; exact (BoundedInterval.bisect_length_sum (B.side i)).symm
  -- Rewrite RHS using the sum identity
  have h_rhs : ∏ i, |(B.side i)|ₗ = ∏ i, (|(B.side i).bisect.fst|ₗ + |(B.side i).bisect.snd|ₗ) := by
    apply Finset.prod_congr rfl; intro i _; exact h_sum i
  rw [h_rhs, Fin.prod_add_eq_sum_prod_choice d _ _]
  -- The mapping from choice to box
  let g : (Fin d → Bool) → Box d := fun c =>
    { side := fun i => let (l, r) := (B.side i).bisect; if c i then r else l }
  -- Key: volume of g c equals the product of half-lengths
  have h_vol_eq : ∀ c : Fin d → Bool, |g c|ᵥ =
      ∏ i, (if c i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ) := by
    intro c; unfold Box.volume; apply Finset.prod_congr rfl; intro i _
    simp only [g]; split_ifs <;> rfl
  -- Two choices give same product when they map to same box
  have h_prod_eq : ∀ c₁ c₂ : Fin d → Bool, g c₁ = g c₂ →
      (∏ i, (if c₁ i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ)) =
      (∏ i, (if c₂ i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ)) := by
    intro c₁ c₂ heq
    apply Finset.prod_congr rfl; intro i _
    have hside : (g c₁).side i = (g c₂).side i := congrArg (·.side i) heq
    simp only [g] at hside
    cases hc₁ : c₁ i <;> cases hc₂ : c₂ i <;> simp only [hc₁, hc₂, ↓reduceIte, Bool.false_eq_true] at hside ⊢
    -- true/false case: hside : bisect.snd = bisect.fst
    · rw [congrArg BoundedInterval.length hside]
    -- false/true case: hside : bisect.fst = bisect.snd
    · rw [congrArg BoundedInterval.length hside]
  -- Use sum_image' which handles non-injective maps
  let h_func : (Fin d → Bool) → ℝ := fun c =>
    ∏ i, (if c i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ)
  have h_fiber : ∀ c ∈ Finset.univ, |g c|ᵥ = ∑ j ∈ Finset.univ with g j = g c, h_func j := by
    intro c _
    rw [h_vol_eq c]
    have h_fib_eq : ∀ j ∈ Finset.univ, g j = g c → h_func j = h_func c := by
      intro j _ hgj; exact h_prod_eq j c hgj
    -- Goal: h_func c = ∑ j with g j = g c, h_func j
    -- All elements in fiber have value h_func c, so sum = card * h_func c
    conv_rhs => rw [show ∑ j ∈ Finset.univ with g j = g c, h_func j =
        ∑ j ∈ Finset.univ.filter (fun j => g j = g c), h_func j from rfl]
    rw [Finset.sum_eq_card_nsmul (fun x hx => by
      rw [Finset.mem_filter] at hx; exact h_fib_eq x hx.1 hx.2)]
    rw [nsmul_eq_mul]
    -- Need: h_func c = card * h_func c. Holds when card = 1 OR h_func c = 0.
    by_cases h_card : (Finset.univ.filter (fun j => g j = g c)).card = 1
    · simp only [h_card, Nat.cast_one, one_mul]; rfl
    · -- Card ≠ 1, and card ≥ 1 (since c is in fiber), so card > 1
      have h_card_pos : 0 < (Finset.univ.filter (fun j => g j = g c)).card := by
        apply Finset.card_pos.mpr; use c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h_card_gt : 1 < (Finset.univ.filter (fun j => g j = g c)).card := by omega
      obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := Finset.one_lt_card.mp h_card_gt
      rw [Finset.mem_filter] at hc₁ hc₂
      -- c₁ and c₂ differ at some coordinate
      have ⟨i, hi_ne⟩ : ∃ i, c₁ i ≠ c₂ i := by
        by_contra h; push_neg at h; exact hne (funext h)
      -- At that coordinate, g c₁ = g c₂ implies bisect.fst = bisect.snd
      have hside : (g c₁).side i = (g c₂).side i := congrArg (·.side i) (hc₁.2.trans hc₂.2.symm)
      simp only [g] at hside
      -- Extract bisect equality from hside by case analysis on c₁ i and c₂ i
      have h_bisect_eq : (B.side i).bisect.fst = (B.side i).bisect.snd := by
        cases hc₁i : c₁ i <;> cases hc₂i : c₂ i <;>
        simp only [hc₁i, hc₂i, Bool.false_eq_true, ↓reduceIte] at hside hi_ne
        · exact (hi_ne rfl).elim  -- false/false case: contradiction
        · exact hside             -- false/true case: hside : fst = snd
        · exact hside.symm        -- true/false case: hside : snd = fst
        · exact (hi_ne rfl).elim  -- true/true case: contradiction
      -- When fst = snd, the interval is degenerate (point), so length = 0
      have h_len_zero : |(B.side i).bisect.snd|ₗ = 0 := by
        rw [← h_bisect_eq]
        -- bisect.fst = bisect.snd means Icc a m = Icc m b, so a = m = b
        unfold BoundedInterval.bisect BoundedInterval.midpoint BoundedInterval.endpoints at h_bisect_eq
        cases hI : B.side i with
        | Ioo a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
        | Icc a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
        | Ioc a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
        | Ico a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
      -- h_func c has a zero factor at coordinate i, so the product is 0
      have h_len_fst_zero : |(B.side i).bisect.fst|ₗ = 0 := by rw [h_bisect_eq]; exact h_len_zero
      have h_prod_zero : h_func c = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        cases hci : c i
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact h_len_fst_zero
        · simp only [↓reduceIte]; exact h_len_zero
      simp only [h_prod_zero, mul_zero]
      -- Goal: h_func c = 0, which is exactly h_prod_zero
      exact h_prod_zero
  rw [Finset.sum_image' h_func h_fiber]

/-- Each sub-box of a subdivision has diameter at most the original diameter divided by √2.
    This follows because each side is halved, reducing the diagonal by a factor related to √2.
    Note: The hypothesis that B is nonempty is necessary because bisection always creates closed
    intervals, which can turn degenerate open intervals ({given -show}`a` {lean}`Ioo a a`) into
    nonempty singletons. -/
lemma subdivide_diameter_bound {d:ℕ} (B: Box d) (hB : B.toSet.Nonempty) :
    ∀ B' ∈ B.subdivide, B'.diameter ≤ B.diameter / Real.sqrt 2 := by
  intro B' hB'
  -- Extract the choice function that defines B'
  unfold subdivide at hB'
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hB'
  obtain ⟨choice, rfl⟩ := hB'
  -- Abbreviate the sub-box for readability
  set B' : Box d := { side := fun i => if choice i then (B.side i).bisect.snd
      else (B.side i).bisect.fst } with hB'_def
  -- Key: B'.diameter ≤ B.diameter / 2 ≤ B.diameter / √2
  -- Since √2 < 2, we have B.diameter / 2 ≤ B.diameter / √2
  suffices h : B'.diameter ≤ B.diameter / 2 by
    calc B'.diameter
        ≤ B.diameter / 2 := h
      _ ≤ B.diameter / √2 := by
          apply div_le_div_of_nonneg_left (diameter_nonneg B)
          · exact Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
          · calc √2 ≤ √4 := Real.sqrt_le_sqrt (by norm_num : (2:ℝ) ≤ 4)
              _ = 2 := by norm_num
  -- Now prove B'.diameter ≤ B.diameter / 2
  -- Key: |B'.side i|ₗ = |B.side i|ₗ / 2 for all i, so diagonal is halved
  -- From nonemptiness of B, each side interval is nonempty
  have h_side_nonempty : ∀ i, (B.side i).toSet.Nonempty := by
    intro i; obtain ⟨x, hx⟩ := hB
    exact ⟨x i, hx i⟩
  -- First show B' is nonempty (the midpoint of each side is in both halves)
  have hB'_nonempty : B'.toSet.Nonempty := by
    use .toLp 2 (fun i => (B.side i).midpoint)
    intro i
    simp only [hB'_def]
    split_ifs with h
    · exact BoundedInterval.midpoint_mem_bisect_snd (B.side i) (h_side_nonempty i)
    · exact BoundedInterval.midpoint_mem_bisect_fst (B.side i) (h_side_nonempty i)
  -- Each side of B' has half the length of B's side
  have h_side_half : ∀ i, |B'.side i|ₗ = |B.side i|ₗ / 2 := by
    intro i
    simp only [hB'_def]
    split_ifs with h
    · exact BoundedInterval.bisect_snd_length _
    · exact BoundedInterval.bisect_fst_length _
  -- Use diameter_eq_sqrt_sum_sq for both boxes
  rw [diameter_eq_sqrt_sum_sq B' hB'_nonempty, diameter_eq_sqrt_sum_sq B hB]
  -- √(∑ (side/2)²) = √(∑ side²) / 2
  have h_sum_eq : ∑ i, |B'.side i|ₗ^2 = (∑ i, |B.side i|ₗ^2) / 4 := by
    simp_rw [h_side_half, div_pow]
    rw [Finset.sum_div]
    ring_nf
  rw [h_sum_eq, Real.sqrt_div (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  norm_num

end Box
