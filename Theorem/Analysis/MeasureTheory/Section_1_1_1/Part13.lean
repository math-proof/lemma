import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Def.Analysis.MeasureTheory.Section_1_1_1.Part4
open BoundedInterval


@[simp]
theorem BoundedInterval.mk'_a (a b : ℝ) (lclosed uclosed : Bool) :
    (mk' a b lclosed uclosed).a = a := by cases lclosed <;> cases uclosed <;> rfl

@[simp]
theorem BoundedInterval.mk'_b (a b : ℝ) (lclosed uclosed : Bool) :
    (mk' a b lclosed uclosed).b = b := by cases lclosed <;> cases uclosed <;> rfl

@[simp]
theorem BoundedInterval.mk'_lclosed (a b : ℝ) (lclosed uclosed : Bool) :
    (mk' a b lclosed uclosed).lclosed = lclosed := by cases lclosed <;> cases uclosed <;> rfl

@[simp]
theorem BoundedInterval.mk'_uclosed (a b : ℝ) (lclosed uclosed : Bool) :
    (mk' a b lclosed uclosed).uclosed = uclosed := by cases lclosed <;> cases uclosed <;> rfl

theorem BoundedInterval.mem_iff' (I: BoundedInterval) (x:ℝ) :
    x ∈ (I:Set ℝ) ↔
      ((if I.lclosed then I.a ≤ x else I.a < x) ∧ (if I.uclosed then x ≤ I.b else x < I.b)) := by
  cases I <;> simp [toSet, lclosed, uclosed]

/-- The set difference of two bounded intervals is the union of two bounded intervals: the
part of the first below the second, and the part above it. -/
theorem BoundedInterval.sdiff (I J: BoundedInterval) :
    ∃ K₁ K₂ : BoundedInterval, (I:Set ℝ) \ (J:Set ℝ) = (K₁:Set ℝ) ∪ (K₂:Set ℝ) := by
  obtain ⟨K₁, hK₁⟩ := BoundedInterval.inter I (mk' I.a J.a I.lclosed (!J.lclosed))
  obtain ⟨K₂, hK₂⟩ := BoundedInterval.inter I (mk' J.b I.b (!J.uclosed) I.uclosed)
  refine ⟨K₁, K₂, ?_⟩
  rw [← hK₁, ← hK₂]
  ext x
  simp only [Set.mem_diff, Set.mem_union, Set.mem_inter_iff, mem_iff', mk'_a, mk'_b,
    mk'_lclosed, mk'_uclosed]
  cases hIl : I.lclosed <;> cases hIu : I.uclosed <;> cases hJl : J.lclosed <;> cases hJu : J.uclosed <;>
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, reduceIte] <;>
    push_neg <;>
    constructor <;>
    intro h <;>
    grind

/-- The difference of two boxes is elementary: a point of the difference leaves the second box
in some coordinate, and in that coordinate the difference of the two sides is a union of two
intervals. -/
theorem Box.sdiff {d:ℕ} (B C: Box d) : IsElementary (B.toSet \ C.toSet) := by
  classical
  choose K₁ K₂ hK using fun i ↦ BoundedInterval.sdiff (B.side i) (C.side i)
  -- the box obtained from `B` by shrinking side `i` to one of the two pieces
  let piece : Fin d → Bool → Box d := fun i k ↦
    ⟨fun j ↦ if j = i then (if k then K₁ i else K₂ i) else B.side j⟩
  have hpiece_side (i : Fin d) (k : Bool) :
      (piece i k).side i = (if k then K₁ i else K₂ i) := by simp [piece]
  have hsub (i : Fin d) (k : Bool) :
      ((if k then K₁ i else K₂ i : BoundedInterval) : Set ℝ) ⊆
        (B.side i : Set ℝ) \ (C.side i : Set ℝ) := by
    rw [hK i]
    cases k <;> simp
  refine ⟨Finset.univ.image (fun p : Fin d × Bool ↦ piece p.1 p.2), ?_⟩
  ext x
  simp only [Set.mem_diff, Box.mem_toSet, Set.mem_iUnion, Finset.mem_image, Finset.mem_univ,
    true_and, exists_prop]
  constructor
  · rintro ⟨hxB, hxC⟩
    obtain ⟨i, hi⟩ : ∃ i, x i ∉ (C.side i : Set ℝ) := by
      by_contra hc
      push_neg at hc
      exact hxC (fun i ↦ hc i)
    have : x i ∈ ((K₁ i : Set ℝ)) ∪ ((K₂ i : Set ℝ)) := by
      rw [← hK i]; exact ⟨hxB i, hi⟩
    rcases this with h | h
    · refine ⟨piece i true, ⟨⟨(i, true), rfl⟩, ?_⟩⟩
      intro j
      by_cases hj : j = i
      · subst hj; simpa [piece] using h
      · simpa [piece, hj] using hxB j
    · refine ⟨piece i false, ⟨⟨(i, false), rfl⟩, ?_⟩⟩
      intro j
      by_cases hj : j = i
      · subst hj; simpa [piece] using h
      · simpa [piece, hj] using hxB j
  · rintro ⟨P, ⟨⟨⟨i, k⟩, rfl⟩, hxP⟩⟩
    have hxi : x i ∈ (B.side i : Set ℝ) \ (C.side i : Set ℝ) := by
      have := hxP i
      rw [hpiece_side] at this
      exact hsub i k this
    refine ⟨fun j ↦ ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; exact hxi.1
      · simpa [piece, hj] using hxP j
    · intro hxC
      exact hxi.2 (hxC i)

/-- Exercise 1.1.1 (Boolean closure): The set difference of two elementary sets is elementary. -/
theorem IsElementary.sdiff {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E \ F) := by
  classical
  obtain ⟨T, rfl⟩ := hF
  induction T using Finset.induction_on with
  | empty => simpa using hE
  | insert C T' hC ih =>
    have hrw : E \ (⋃ B ∈ insert C T', (B:Set (EuclideanSpace' d)))
        = (E \ ⋃ B ∈ T', (B:Set (EuclideanSpace' d))) \ C.toSet := by
      rw [Finset.set_biUnion_insert, Set.diff_diff, Set.union_comm]
    rw [hrw]
    obtain ⟨S, hS⟩ := ih
    rw [hS]
    have hdiff : (⋃ B ∈ S, (B:Set (EuclideanSpace' d))) \ C.toSet
        = ⋃ B ∈ S, ((B:Set (EuclideanSpace' d)) \ C.toSet) := by
      ext y; simp only [Set.mem_diff, Set.mem_iUnion, exists_prop]; tauto
    rw [hdiff]
    have : (⋃ B ∈ S, ((B:Set (EuclideanSpace' d)) \ C.toSet))
        = ⋃ X ∈ S.image (fun B : Box d ↦ (B:Set (EuclideanSpace' d)) \ C.toSet), X := by
      ext y
      simp only [Set.mem_iUnion, Finset.mem_image, exists_prop]
      constructor
      · rintro ⟨B, hB, hy⟩; exact ⟨_, ⟨B, hB, rfl⟩, hy⟩
      · rintro ⟨X, ⟨B, hB, rfl⟩, hy⟩; exact ⟨B, hB, hy⟩
    rw [this]
    refine IsElementary.union' ?_
    intro X hX
    simp only [Finset.mem_image] at hX
    obtain ⟨B, -, rfl⟩ := hX
    exact Box.sdiff B C

/-- Exercise 1.1.1 (Boolean closure): The symmetric difference of two elementary sets is elementary. -/
theorem IsElementary.symmDiff {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (symmDiff E F) := by
  have := (hE.sdiff hF).union (hF.sdiff hE)
  simpa [Set.symmDiff_def] using this

open Pointwise

/-- Translating a bounded interval gives a bounded interval with the same open/closed ends. -/
theorem BoundedInterval.translate (I: BoundedInterval) (c:ℝ) :
    ((mk' (I.a + c) (I.b + c) I.lclosed I.uclosed : BoundedInterval) : Set ℝ)
      = (I:Set ℝ) + {c} := by
  ext y
  simp only [mem_iff', mk'_a, mk'_b, mk'_lclosed, mk'_uclosed, Set.add_singleton,
    Set.mem_image]
  constructor
  · intro hy
    refine ⟨y - c, ?_, by ring⟩
    revert hy
    cases I.lclosed <;> cases I.uclosed <;> simp only [if_true, if_false,
      Bool.false_eq_true] <;> grind
  · rintro ⟨z, hz, rfl⟩
    revert hz
    cases I.lclosed <;> cases I.uclosed <;> simp only [if_true, if_false,
      Bool.false_eq_true] <;> grind

/-- Translating a box gives a box. -/
theorem Box.translate {d:ℕ} (B: Box d) (x: EuclideanSpace' d) :
    ∃ B' : Box d, (B':Set (EuclideanSpace' d)) = (B:Set (EuclideanSpace' d)) + {x} := by
  let I' : Fin d → BoundedInterval := fun i ↦
    BoundedInterval.mk' ((B.side i).a + x i) ((B.side i).b + x i)
      (B.side i).lclosed (B.side i).uclosed
  have hI' (i : Fin d) : (I' i : Set ℝ) = ((B.side i : Set ℝ)) + {x i} :=
    BoundedInterval.translate (B.side i) (x i)
  refine ⟨⟨I'⟩, ?_⟩
  ext y
  simp only [Box.mem_toSet]
  constructor
  · intro hy
    apply Set.mem_add.mpr
    refine ⟨.toLp 2 (fun i ↦ y i - x i), ?_, x, rfl, by apply PiLp.ext; intro i; simp⟩
    simp only [Box.mem_toSet]; intro i
    have : y i ∈ (I' i : Set ℝ) := hy i
    rw [hI' i] at this
    obtain ⟨a, ha, b, rfl, hab⟩ := this
    convert ha using 1; linarith
  · intro hy
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hy
    rw [Set.mem_singleton_iff.mp hb] at hab
    simp only [Box.mem_toSet] at ha
    intro i
    rw [hI' i]
    exact Set.mem_add.mpr ⟨a i, ha i, x i, rfl,
      by have := congr_fun (congrArg WithLp.ofLp hab) i; simpa using this⟩

/-- Exercise 1.1.1 (Boolean closure): Translation of an elementary set is elementary. -/
theorem IsElementary.translate {d:ℕ} {E: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (x: EuclideanSpace' d) : IsElementary (E + {x}) := by
  classical
  obtain ⟨S, rfl⟩ := hE
  choose f hf using fun B : Box d ↦ Box.translate B x
  refine ⟨S.image f, ?_⟩
  ext y
  simp only [Set.mem_iUnion, Finset.mem_image, exists_prop]
  constructor
  · intro hy
    obtain ⟨z, hz, w, hw, hzw⟩ := Set.mem_add.mp hy
    rw [Set.mem_singleton_iff.mp hw] at hzw
    obtain ⟨B, hB, hzB⟩ : ∃ B ∈ S, z ∈ (B:Set (EuclideanSpace' d)) := by simpa using hz
    refine ⟨f B, ⟨B, hB, rfl⟩, ?_⟩
    rw [hf B, ← hzw]
    exact Set.mem_add.mpr ⟨z, hzB, x, rfl, rfl⟩
  · rintro ⟨D, ⟨B, hB, rfl⟩, hyD⟩
    rw [hf B] at hyD
    obtain ⟨z, hzB, w, hw, hzw⟩ := Set.mem_add.mp hyD
    rw [Set.mem_singleton_iff.mp hw] at hzw
    exact Set.mem_add.mpr ⟨z, by simpa using Set.mem_biUnion hB hzB, x, rfl, hzw⟩

/-- A sublemma for proving Lemma 1.1.2(i): Any finset of intervals admits a common
refinement into pairwise disjoint sub-intervals. -/
theorem BoundedInterval.partition (S: Finset BoundedInterval) : ∃ T: Finset BoundedInterval, (T : Set _).PairwiseDisjoint BoundedInterval.toSet ∧ ∀ I ∈ S, ∃ U : Set T, I = ⋃ J ∈ U, J.val.toSet := by
  let endpoints : Finset ℝ := S.image BoundedInterval.a ∪ S.image BoundedInterval.b
  have ha_mem {I:BoundedInterval} (hI: I ∈ S) : I.a ∈ endpoints := by grind
  have hb_mem {I:BoundedInterval} (hI: I ∈ S) : I.b ∈ endpoints := by grind
  let k := endpoints.card
  let sorted : Fin k ≃o endpoints := endpoints.orderIsoOfFin (by rfl)
  let a : ℕ → ℝ := fun n ↦ if h:n < k then sorted ⟨n,h⟩ else 0  -- 0 is a junk value
  let T := Finset.univ.image (fun x:endpoints ↦ Icc x x)
    ∪ (Finset.range (k-1)).image (fun n ↦ Ioo (a n) (a (n+1)))
  refine' ⟨T,_,_⟩
  . rw [Set.pairwiseDisjoint_iff]
    intro I hI J hJ hIJ
    have := hIJ.some_mem
    simp_all [T]
    obtain ⟨ x, hx, rfl ⟩ | ⟨ n, hn, rfl ⟩ := hI
      <;> obtain ⟨ y, hy, rfl ⟩ | ⟨ m, hm, rfl ⟩ := hJ
      <;> simp at this
    . rw [show x=y by grind]
    . rw [this.1] at this
      set n := sorted.symm ⟨ x, hx ⟩
      have hax : x = sorted n := by simp [n]
      obtain ⟨ n, hn ⟩ := n
      simp [a, show m < k by omega, show m+1 < k by omega, hax] at this
      omega
    . rw [this.2] at this
      set m := sorted.symm ⟨ y, hy ⟩
      have hay : y = sorted m := by simp [m]
      obtain ⟨ m, hm ⟩ := m
      simp [a, show n < k by omega, show n+1 < k by omega, hay] at this
      omega
    have h1 : a n < a (m+1) := this.1.1.trans this.2.2
    have h2 : a m < a (n+1) := this.2.1.trans this.1.2
    simp [a, show n < k by omega, show n+1 < k by omega,
          show m < k by omega, show m+1 < k by omega] at h1 h2
    rw [show n=m by omega]
  intro I hI
  use {J | J.val ⊆ I }
  ext x; simp; constructor
  . intro hx
    by_cases hend : x ∈ endpoints
    . use Icc x x; simp [T, hx, hend]
    let n := sorted.symm ⟨ I.a, ha_mem hI ⟩
    let m := sorted.symm ⟨ I.b, hb_mem hI ⟩
    have hnI : I.a = sorted n := by simp [n]
    have hmI : I.b = sorted m := by simp [m]
    obtain ⟨ m, hm ⟩ := m; obtain ⟨ n, hn ⟩ := n
    apply I.subset_Icc at hx
    simp [hnI, hmI] at hx
    obtain ⟨ hx1, hx2 ⟩ := hx
    have H : ∃ m, x ≤ a m := by use m; grind
    let r := Nat.find H
    have hrm : r ≤ m := by convert Nat.find_min' H _; grind
    have hr : r < k := by linarith
    have hxr : x ≤ sorted ⟨ r, hr ⟩ := by convert Nat.find_spec H; grind
    have hnr : n < r := by
      by_contra!
      replace : (sorted ⟨r, hr⟩).val ≤ (sorted ⟨n, hn⟩).val := by
        simp only [Subtype.coe_le_coe]
        apply sorted.monotone; simpa
      simp [show x = sorted ⟨ n, hn ⟩ by order] at hend
    refine' ⟨ Ioo (sorted ⟨ r-1, by omega ⟩) (sorted ⟨ r, hr ⟩), _ , _, _ ⟩
    . apply Set.Subset.trans _ I.Ioo_subset
      simp [hnI, hmI]
      apply Set.Ioo_subset_Ioo <;> simp [Subtype.coe_le_coe] <;> omega
    . simp [T]; refine' ⟨ r-1, by omega, _ ⟩
      simp [a, show r-1 < k by omega, show r < k by omega, show r-1+1=r by omega]
    simp
    have h1 : x ≠ sorted ⟨ r, hr ⟩ := by by_contra!; simp [this] at hend
    have h3 : sorted ⟨ r-1, by omega ⟩ < x := by
      by_contra!
      convert Nat.find_min H (show r-1 < r by omega) _
      simp [a, show r-1 < k by omega, this]
    exact ⟨h3, by order⟩
  rintro ⟨a, ha_sub, _, ha_mem⟩; exact ha_sub ha_mem

/-- Lemma 1.1.2(i): Any finset of boxes admits a common refinement into pairwise disjoint sub-boxes. -/
theorem Box.partition {d:ℕ} (S: Finset (Box d)) : ∃ T: Finset (Box d), (T : Set (Box d)).PairwiseDisjoint Box.toSet ∧ ∀ I ∈ S, ∃ U : Set T, I = ⋃ J ∈ U, J.val.toSet := by
  choose T hTdisj hT using BoundedInterval.partition
  let J : Fin d → Finset BoundedInterval := fun i ↦ T (S.image (fun B ↦ B.side i))
  have hJdisj (i:Fin d) : (J i : Set _).PairwiseDisjoint BoundedInterval.toSet :=
    hTdisj (S.image (fun B ↦ B.side i))
  have hJ (i:Fin d) {B: Box d} (hB: B ∈ S) : ∃ U : Set (J i), B.side i = ⋃ K ∈ U, K.val.toSet := by
    apply hT (S.image (fun B ↦ B.side i)) (B.side i); simp; use B
  classical
  refine' ⟨ (Finset.univ.pi J).image (fun I ↦ ⟨ fun i ↦ I i (by simp) ⟩ ) , _, _ ⟩
  . rw [Set.pairwiseDisjoint_iff]
    intro B₁ hB₁ B₂ hB₂ hB₁B₂; simp at hB₁ hB₂
    obtain ⟨ J₁, hJ₁, rfl ⟩ := hB₁
    obtain ⟨ J₂, hJ₂, rfl ⟩ := hB₂
    ext i; simp
    have := hB₁B₂.some_mem
    simp at this
    obtain ⟨ h₁, h₂ ⟩ := this
    specialize hJdisj i; rw [Set.pairwiseDisjoint_iff] at hJdisj
    apply_rules [hJdisj, Set.nonempty_of_mem (x := (hB₁B₂.some i))]
    grind
  intro B hB
  choose U hU using hJ
  use {B' | ∀ i, ∃ hi : B'.val.side i ∈ J i, ⟨ _, hi ⟩ ∈ U i hB}
  ext x; simp only [Box.mem_toSet, Set.mem_iUnion, Set.mem_setOf_eq, Subtype.exists]
  constructor
  . intro h
    have h' : ∀ i, x i ∈ ⋃ K ∈ U i hB, (K:BoundedInterval).toSet := by
      intro i; rw [← hU i hB]; exact h i
    simp only [Set.mem_iUnion] at h'
    choose I hI₁ hI₂ using h'
    refine' ⟨ ⟨ fun i ↦ (I i).1 ⟩, ?_, fun i ↦ ⟨(I i).2, hI₁ i⟩, fun i ↦ hI₂ i ⟩
    · exact Finset.mem_image.mpr ⟨fun i _ ↦ I i, Finset.mem_pi.mpr (fun i _ ↦ by simp), by ext i; simp⟩
  rintro ⟨ B', h1, h2, h3 ⟩ i
  rw [hU i hB]; simp only [Set.mem_iUnion]
  obtain ⟨hi, hU'⟩ := h2 i
  exact ⟨⟨B'.side i, hi⟩, hU', h3 i⟩

/-- Every elementary set can be partitioned into pairwise disjoint boxes. -/
theorem IsElementary.partition {d:ℕ} {E: Set (EuclideanSpace' d)}
(hE: IsElementary E) : ∃ T: Finset (Box d), (T : Set (Box d)).PairwiseDisjoint Box.toSet ∧ E = ⋃ J ∈ T, J.toSet := by
  obtain ⟨ S, rfl ⟩ := hE
  have ⟨ T', hT', hST' ⟩ := Box.partition S
  choose U hU using hST'
  conv => rhs; ext T; rhs; lhs; rhs; ext B; rhs; ext h; rw [hU B h]
  classical
  use T'.filter (fun J ↦ ∃ B, ∃ h:B ∈ S, J ∈ Subtype.val '' (U B h))
  simp; split_ands
  . apply hT'.subset; intro _; simp; tauto
  ext; simp; grind

/-- Helper lemma for Lemma 1.1.2(ii): The set of lattice points (multiples of 1/N) in an interval is finite. -/
theorem BoundedInterval.sample_finite (I : BoundedInterval) {N:ℕ} (hN: N ≠ 0):
  Finite ↥(I.toSet ∩ (Set.range (fun n:ℤ ↦ (N:ℝ)⁻¹*n))) := by
  rw [Set.finite_coe_iff]
  apply Set.Finite.subset _ (Set.inter_subset_inter_left _ (BoundedInterval.subset_Icc I))
  suffices Set.Finite (Set.Icc I.a I.b ∩ Set.range (fun n:ℤ ↦ (N:ℝ)⁻¹*n)) by exact this
  have : Set.Icc I.a I.b ∩ Set.range (fun n:ℤ ↦ (N:ℝ)⁻¹*n) ⊆
         (fun n:ℤ ↦ (N:ℝ)⁻¹*n) '' (Finset.Icc ⌈(N:ℝ) * I.a⌉ ⌊(N:ℝ) * I.b⌋:Set ℤ) := by
    intro x ⟨hx_in_Icc, n, hn⟩
    simp at hn; subst hn
    refine ⟨n, ?_, rfl⟩
    simp only [Finset.mem_coe]
    rw [Finset.mem_Icc]
    constructor
    · have : I.a ≤ (N:ℝ)⁻¹ * n := hx_in_Icc.1
      have hN_pos : (0:ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
      have : (N:ℝ) * I.a ≤ n := by
        calc (N:ℝ) * I.a ≤ (N:ℝ) * ((N:ℝ)⁻¹ * n) := by nlinarith
             _ = n := by field_simp
      exact Int.ceil_le.mpr this
    · have : (N:ℝ)⁻¹ * n ≤ I.b := hx_in_Icc.2
      have hN_pos : (0:ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
      have : n ≤ (N:ℝ) * I.b := by
        calc n = (N:ℝ) * ((N:ℝ)⁻¹ * n) := by field_simp
             _ ≤ (N:ℝ) * I.b := by nlinarith
      exact Int.le_floor.mpr this
  exact Set.Finite.subset ((Finset.finite_toSet _).image _) this

