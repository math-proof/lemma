import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Abbrev.Analysis.MeasureTheory.Section_1_1_1.Part7
open BoundedInterval

open Pointwise


/-- Unfold {name}`Box.prod` on a coordinate. -/
lemma Box.prod_side {d₁ d₂:ℕ} (B₁: Box d₁) (B₂: Box d₂) (i : Fin (d₁ + d₂)) :
    (B₁.prod B₂).side i =
      if h : (i : ℕ) < d₁ then B₁.side ⟨i, h⟩
      else B₂.side ⟨(i : ℕ) - d₁, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) i.isLt⟩ := by
  rcases i with ⟨i, hi⟩
  rfl

/-- Coordinate of a product vector in the first block. -/
lemma EuclideanSpace'.prod_equiv_symm_apply_left {d₁ d₂:ℕ}
    (y : EuclideanSpace' d₁) (z : EuclideanSpace' d₂) {i : ℕ} (hi : i < d₁) :
    (EuclideanSpace'.prod_equiv d₁ d₂).symm (y, z) ⟨i, Nat.lt_add_right d₂ hi⟩ = y ⟨i, hi⟩ := by
  simp [EuclideanSpace'.prod_equiv, dif_pos hi]

/-- Coordinate of a product vector in the second block. -/
lemma EuclideanSpace'.prod_equiv_symm_apply_right {d₁ d₂:ℕ}
    (y : EuclideanSpace' d₁) (z : EuclideanSpace' d₂) {j : ℕ} (hj : j < d₂) :
    (EuclideanSpace'.prod_equiv d₁ d₂).symm (y, z) ⟨d₁ + j, Nat.add_lt_add_left hj d₁⟩ =
      z ⟨j, hj⟩ := by
  have hnot : ¬ d₁ + j < d₁ := Nat.not_lt.mpr (Nat.le_add_right _ _)
  simp [EuclideanSpace'.prod_equiv, dif_neg hnot, Nat.add_sub_cancel_left]

/-- First factor of {name}`prod_equiv`. -/
lemma EuclideanSpace'.prod_equiv_apply_fst {d₁ d₂:ℕ}
    (x : EuclideanSpace' (d₁ + d₂)) (i : Fin d₁) :
    (EuclideanSpace'.prod_equiv d₁ d₂ x).1 i = x ⟨i, Nat.lt_add_right d₂ i.isLt⟩ := by
  simp [EuclideanSpace'.prod_equiv]

/-- Second factor of {name}`prod_equiv`. Matches `toFun`, which uses `i + d₁`. -/
lemma EuclideanSpace'.prod_equiv_apply_snd {d₁ d₂:ℕ}
    (x : EuclideanSpace' (d₁ + d₂)) (j : Fin d₂) :
    (EuclideanSpace'.prod_equiv d₁ d₂ x).2 j =
      x ⟨(j : ℕ) + d₁, by omega⟩ := by
  simp [EuclideanSpace'.prod_equiv]

/-- The set of a product box is the Cartesian product of the two boxes. -/
lemma Box.prod_toSet {d₁ d₂:ℕ} (B₁: Box d₁) (B₂: Box d₂) :
    EuclideanSpace'.prod B₁.toSet B₂.toSet = (B₁.prod B₂).toSet := by
  ext x
  constructor
  · rintro ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩
    intro i
    rcases i with ⟨i, hi⟩
    simp only [Box.prod]
    split_ifs with h
    · simp [EuclideanSpace'.prod_equiv, dif_pos h]
      exact hy ⟨i, h⟩
    · simp [EuclideanSpace'.prod_equiv, dif_neg h]
      exact hz ⟨i - d₁, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) hi⟩
  · intro hx
    refine ⟨⟨(EuclideanSpace'.prod_equiv d₁ d₂ x).1, (EuclideanSpace'.prod_equiv d₁ d₂ x).2⟩, ?_,
      (EuclideanSpace'.prod_equiv d₁ d₂).left_inv x⟩
    constructor
    · intro i
      have hx' := hx ⟨(i : ℕ), Nat.lt_add_right d₂ i.isLt⟩
      simp [Box.prod, EuclideanSpace'.prod_equiv, dif_pos i.isLt] at hx' ⊢
      exact hx'
    · intro j
      have hnot : ¬ (j : ℕ) + d₁ < d₁ := Nat.not_lt.mpr (Nat.le_add_left d₁ _)
      have hx' := hx ⟨(j : ℕ) + d₁, by omega⟩
      simp [Box.prod, EuclideanSpace'.prod_equiv, dif_neg hnot] at hx' ⊢
      convert hx' <;> (apply Fin.ext; exact Nat.add_sub_cancel (j : ℕ) d₁)

/-- Recovering the factors from a product box. -/
lemma Box.prod_injective {d₁ d₂:ℕ} :
    Function.Injective (fun p : Box d₁ × Box d₂ => p.1.prod p.2) := by
  intro ⟨B₁, C₁⟩ ⟨B₂, C₂⟩ h
  have hside := congrArg Box.side h
  refine Prod.ext ?_ ?_
  · ext i
    have := congrFun hside ⟨i, Nat.lt_add_right d₂ i.isLt⟩
    rw [Box.prod_side, Box.prod_side, dif_pos i.isLt, dif_pos i.isLt] at this
    exact this
  · ext j
    have hnot : ¬ (j : ℕ) + d₁ < d₁ := Nat.not_lt.mpr (Nat.le_add_left d₁ _)
    have := congrFun hside ⟨(j : ℕ) + d₁, by omega⟩
    rw [Box.prod_side, Box.prod_side, dif_neg hnot, dif_neg hnot] at this
    have hj (C : Box d₂) : C.side ⟨(j : ℕ) + d₁ - d₁,
        Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp hnot)
          (by omega)⟩ = C.side j :=
      congrArg C.side (Fin.eq_of_val_eq (Nat.add_sub_cancel (j : ℕ) d₁))
    rwa [hj C₁, hj C₂] at this

/-- Volume of a product box is the product of the volumes. -/
lemma Box.volume_prod {d₁ d₂:ℕ} (B₁: Box d₁) (B₂: Box d₂) :
    |(B₁.prod B₂)|ᵥ = |B₁|ᵥ * |B₂|ᵥ := by
  simp only [Box.volume]
  rw [Fin.prod_univ_add]
  refine congrArg₂ (· * ·) ?_ ?_
  · apply Finset.prod_congr rfl
    intro i _
    simp [Box.prod]
  · apply Finset.prod_congr rfl
    intro j _
    simp [Box.prod] <;>
      (apply Fin.ext; simp [Fin.natAdd, Nat.add_sub_cancel_left])

/-- Exercise 1.1.4: The Cartesian product of two elementary sets is elementary. -/
theorem IsElementary.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: IsElementary E₁) (hE₂: IsElementary E₂) : IsElementary (EuclideanSpace'.prod E₁ E₂) := by
  obtain ⟨S, rfl⟩ := hE₁
  obtain ⟨T, rfl⟩ := hE₂
  refine ⟨(S ×ˢ T).image (fun p => p.1.prod p.2), ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩ := hx
    rw [Set.mem_iUnion₂] at hy hz ⊢
    obtain ⟨B, hB, hyB⟩ := hy
    obtain ⟨C, hC, hzC⟩ := hz
    exact ⟨B.prod C,
      Finset.mem_image.mpr ⟨⟨B, C⟩, Finset.mem_product.mpr ⟨hB, hC⟩, rfl⟩,
      by
        rw [← Box.prod_toSet]
        exact ⟨⟨y, z⟩, ⟨hyB, hzC⟩, rfl⟩⟩
  · intro hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨BC, hBC, hxBC⟩ := hx
    obtain ⟨⟨B, C⟩, hBC', rfl⟩ := Finset.mem_image.mp hBC
    obtain ⟨hB, hC⟩ := Finset.mem_product.mp hBC'
    rw [← Box.prod_toSet] at hxBC
    obtain ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩ := hxBC
    exact ⟨⟨y, z⟩,
      ⟨Set.mem_iUnion₂.mpr ⟨B, hB, hy⟩, Set.mem_iUnion₂.mpr ⟨C, hC, hz⟩⟩, rfl⟩

/-- The product of two pairwise disjoint box families remains pairwise disjoint. -/
lemma Box.prod_pairwiseDisjoint {d₁ d₂:ℕ} {S : Finset (Box d₁)} {T : Finset (Box d₂)}
    (hS : (S : Set (Box d₁)).PairwiseDisjoint Box.toSet)
    (hT : (T : Set (Box d₂)).PairwiseDisjoint Box.toSet) :
    (((S ×ˢ T).image (fun p => p.1.prod p.2) : Finset (Box (d₁ + d₂))) :
      Set (Box (d₁ + d₂))).PairwiseDisjoint Box.toSet := by
  rw [Set.pairwiseDisjoint_iff]
  intro B₁ hB₁ B₂ hB₂ hne
  obtain ⟨⟨C₁, D₁⟩, hmem₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hB₁)
  obtain ⟨⟨C₂, D₂⟩, hmem₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hB₂)
  obtain ⟨hC₁, hD₁⟩ := Finset.mem_product.mp hmem₁
  obtain ⟨hC₂, hD₂⟩ := Finset.mem_product.mp hmem₂
  obtain ⟨x, hx⟩ := hne
  rw [Set.mem_inter_iff, ← Box.prod_toSet, ← Box.prod_toSet] at hx
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨⟨y, z⟩, ⟨hy1, hz1⟩, rfl⟩ := hx1
  obtain ⟨⟨y', z'⟩, ⟨hy2, hz2⟩, hyz⟩ := hx2
  have hyz' : (y, z) = (y', z') :=
    (EuclideanSpace'.prod_equiv d₁ d₂).symm.injective hyz.symm
  rcases hyz' with ⟨rfl, rfl⟩
  have hC : C₁ = C₂ := by
    by_contra hneC
    exact Set.disjoint_left.mp (hS hC₁ hC₂ hneC) hy1 hy2
  have hD : D₁ = D₂ := by
    by_contra hneD
    exact Set.disjoint_left.mp (hT hD₁ hD₂ hneD) hz1 hz2
  subst hC; subst hD
  rfl

/-- Measure is multiplicative on products: μ(E₁ × E₂) = μ(E₁) \* μ(E₂). -/
theorem IsElementary.measure_of_prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: IsElementary E₁) (hE₂: IsElementary E₂)
  : (hE₁.prod hE₂).measure = hE₁.measure * hE₂.measure := by
  classical
  set S := hE₁.partition.choose
  set T := hE₂.partition.choose
  have hS_disj : (S : Set (Box d₁)).PairwiseDisjoint Box.toSet := hE₁.partition.choose_spec.1
  have hT_disj : (T : Set (Box d₂)).PairwiseDisjoint Box.toSet := hE₂.partition.choose_spec.1
  have hE₁_eq : E₁ = ⋃ B ∈ S, B.toSet := hE₁.partition.choose_spec.2
  have hE₂_eq : E₂ = ⋃ C ∈ T, C.toSet := hE₂.partition.choose_spec.2
  set U := (S ×ˢ T).image (fun p => p.1.prod p.2)
  have hU_disj : (U : Set (Box (d₁ + d₂))).PairwiseDisjoint Box.toSet :=
    Box.prod_pairwiseDisjoint hS_disj hT_disj
  have hprod_eq : EuclideanSpace'.prod E₁ E₂ = ⋃ B ∈ U, B.toSet := by
    rw [hE₁_eq, hE₂_eq]
    ext x
    constructor
    · intro hx
      obtain ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩ := hx
      rw [Set.mem_iUnion₂] at hy hz ⊢
      obtain ⟨B, hB, hyB⟩ := hy
      obtain ⟨C, hC, hzC⟩ := hz
      exact ⟨B.prod C,
        Finset.mem_image.mpr ⟨⟨B, C⟩, Finset.mem_product.mpr ⟨hB, hC⟩, rfl⟩,
        by
          rw [← Box.prod_toSet]
          exact ⟨⟨y, z⟩, ⟨hyB, hzC⟩, rfl⟩⟩
    · intro hx
      rw [Set.mem_iUnion₂] at hx
      obtain ⟨BC, hBC, hxBC⟩ := hx
      obtain ⟨⟨B, C⟩, hBC', rfl⟩ := Finset.mem_image.mp hBC
      obtain ⟨hB, hC⟩ := Finset.mem_product.mp hBC'
      rw [← Box.prod_toSet] at hxBC
      obtain ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩ := hxBC
      exact ⟨⟨y, z⟩,
        ⟨Set.mem_iUnion₂.mpr ⟨B, hB, hy⟩, Set.mem_iUnion₂.mpr ⟨C, hC, hz⟩⟩, rfl⟩
  have hmeas : (hE₁.prod hE₂).measure = ∑ B ∈ U, |B|ᵥ :=
    (hE₁.prod hE₂).measure_eq hU_disj hprod_eq
  have hE₁m : hE₁.measure = ∑ B ∈ S, |B|ᵥ := hE₁.measure_eq hS_disj hE₁_eq
  have hE₂m : hE₂.measure = ∑ C ∈ T, |C|ᵥ := hE₂.measure_eq hT_disj hE₂_eq
  have hinj : ∀ p ∈ S ×ˢ T, ∀ q ∈ S ×ˢ T,
      (fun r : Box d₁ × Box d₂ => r.1.prod r.2) p = (fun r => r.1.prod r.2) q → p = q := by
    intro p _ q _ hpq
    exact Box.prod_injective hpq
  rw [hmeas, hE₁m, hE₂m, Finset.sum_image hinj, Finset.sum_product]
  simp_rw [Box.volume_prod]
  rw [Finset.sum_mul_sum]

