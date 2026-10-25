import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
open NPartition
open scoped BigOperators


section
-- ac-theorems


open Finset BigOperators

variable {N : ℕ}

/-- `IsNPartition` is equivalent to `Antitone`. -/
lemma isNPartition_iff_antitone {lam : Fin N → ℕ} : IsNPartition lam ↔ Antitone lam :=
  Iff.rfl

/-- The zero tuple is an N-partition (trivially weakly decreasing). -/
lemma isNPartition_zero : IsNPartition (0 : Fin N → ℕ) := by
  intro i j _
  simp only [Pi.zero_apply, le_refl]

/-- The sum of two N-partitions is an N-partition. -/
lemma IsNPartition.add {α β : Fin N → ℕ} (hα : IsNPartition α) (hβ : IsNPartition β) :
    IsNPartition (α + β) := by
  intro i j hij
  simp only [Pi.add_apply]
  exact Nat.add_le_add (hα i j hij) (hβ i j hij)

namespace NPartition


end NPartition

namespace NPartition

variable {N : ℕ}



/-- Alias for `antitone` to match SchurBasics.lean naming convention.
    The weakly decreasing condition: if `i ≤ j` then `parts j ≤ parts i`. -/
lemma monotone (μ : NPartition N) : ∀ i j : Fin N, i ≤ j → μ.parts j ≤ μ.parts i :=
  μ.antitone

/-- Alias for `antitone` to match PieriJacobiTrudi.lean naming convention.
    The weakly decreasing condition: if `i ≤ j` then `parts j ≤ parts i`. -/
lemma weaklyDecreasing (μ : NPartition N) : ∀ i j : Fin N, i ≤ j → μ.parts j ≤ μ.parts i :=
  μ.antitone

/-- Extensionality in terms of pointwise equality. -/
lemma ext' {μ ν : NPartition N} : μ = ν ↔ ∀ i, μ.parts i = ν.parts i :=
  ⟨fun h _ => h ▸ rfl, fun h => ext (funext h)⟩

lemma le_def (μ ν : NPartition N) : μ ≤ ν ↔ ∀ i, μ.parts i ≤ ν.parts i := Iff.rfl

/-- An N-partition is finite (has finitely many nonzero entries). -/
lemma finite_support (μ : NPartition N) : Set.Finite {i | μ.parts i ≠ 0} :=
  Set.toFinite _

/-- The size of ofPartition p equals n (the sum of the original partition).
    (Proposition prop.sf.Npar-as-par, well-definedness)

    Label: prop.sf.Npar-as-par.size -/
lemma ofPartition_size {n : ℕ} (p : Nat.Partition n) (hp : Multiset.card p.parts ≤ N) :
    (ofPartition p hp).size = n := by
  simp only [size, ofPartition]
  set sorted := p.parts.sort (· ≥ ·) with hsorted_def
  have hlen : sorted.length = Multiset.card p.parts := Multiset.length_sort (· ≥ ·)
  have hsum : sorted.sum = n := by
    rw [← Multiset.sum_coe, Multiset.sort_eq p.parts (· ≥ ·)]
    exact p.parts_sum
  have hsorted_len : sorted.length ≤ N := by rw [hlen]; exact hp
  -- Key: the sum over Fin N equals the sum of the sorted list
  have key : ∑ i : Fin N, (if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0) = sorted.sum := by
    -- sorted.sum = ∑ i : Fin sorted.length, sorted.get i
    have h1 : sorted.sum = ∑ i : Fin sorted.length, sorted.get i := by
      conv_lhs => rw [← List.ofFn_get sorted]
      rw [List.sum_ofFn]
    rw [h1]
    -- Create an embedding from Fin sorted.length to Fin N
    have hemb : ∀ i : Fin sorted.length, (i : ℕ) < N := fun i => Nat.lt_of_lt_of_le i.isLt hsorted_len
    let emb : Fin sorted.length ↪ Fin N := ⟨fun i => ⟨i.val, hemb i⟩, by
      intro i j h; simp only [Fin.mk.injEq] at h; exact Fin.ext h⟩
    -- Split the sum over Fin N into indices in range and out of range
    have h2 : ∑ i : Fin N, (if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0) =
              ∑ i ∈ Finset.univ.map emb, (if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0) +
              ∑ i ∈ Finset.univ \ Finset.univ.map emb, (if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0) := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff)]
      congr 1
      simp [Finset.union_sdiff_of_subset (Finset.subset_univ _)]
    rw [h2]
    -- The sum over indices out of range is 0
    have h3 : ∑ i ∈ Finset.univ \ Finset.univ.map emb, (if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_map, true_and] at hi
      have : ¬ (i.val < sorted.length) := by
        intro hlt
        apply hi
        use ⟨i.val, hlt⟩
        exact Fin.ext rfl
      simp [this]
    rw [h3, Nat.add_zero, Finset.sum_map]
    refine Finset.sum_congr rfl ?_
    intro i _
    have hcoe : emb i = ⟨i.val, hemb i⟩ := rfl
    rw [hcoe, dif_pos i.isLt]
  rw [key, hsum]

/-- The number of non-zero parts of an N-partition is at most N.
    (Proposition prop.sf.Npar-as-par, boundedness) -/
lemma toPartition_card_le (μ : NPartition N) :
    Multiset.card μ.toPartition.parts ≤ N := by
  simp only [toPartition]
  calc Multiset.card ((Finset.univ.val.map μ.parts).filter (· ≠ 0))
      ≤ Multiset.card (Finset.univ.val.map μ.parts) :=
        Multiset.card_le_card (Multiset.filter_le _ _)
    _ = Multiset.card (Finset.univ (α := Fin N)).val := by rw [Multiset.card_map]
    _ = N := by simp
/-- The antitone property as a function (for use in proofs). -/
lemma parts_antitone (μ : NPartition N) : Antitone μ.parts := μ.antitone

/-- An NPartition's parts satisfy the IsNPartition predicate.
    This connects the structure-based definition with the predicate-based definition. -/
lemma isNPartition (μ : NPartition N) : IsNPartition μ.parts :=
  μ.monotone

/-- Extensionality for pointwise equality (variant taking a proof for each index). -/
lemma ext_parts {μ ν : NPartition N} (h : ∀ i, μ.parts i = ν.parts i) : μ = ν :=
  ext (funext h)


@[simp]
lemma zero_parts : (0 : NPartition N).parts = fun _ => 0 := rfl

@[simp]
lemma size_eq_sum (μ : NPartition N) : μ.size = ∑ i, μ.parts i := rfl

@[simp]
lemma zero_size : (0 : NPartition N).size = 0 := by simp [size]

/-- The first entry is the largest in an N-partition (when N > 0). -/
lemma parts_zero_max (μ : NPartition N) (i : Fin N) (hN : 0 < N) :
    μ.parts i ≤ μ.parts ⟨0, hN⟩ := by
  apply μ.antitone
  exact Nat.zero_le i.val

/-- The first entry of an N-partition equals the size iff all other entries are zero. -/
lemma parts_zero_eq_size_iff (μ : NPartition N) (hN : 0 < N) :
    μ.parts ⟨0, hN⟩ = μ.size ↔ ∀ i : Fin N, i.val ≠ 0 → μ.parts i = 0 := by
  constructor
  · intro h i hi
    have hle : μ.parts i ≤ μ.parts ⟨0, hN⟩ := by
      apply μ.antitone
      exact Nat.zero_le i.val
    have hsum : μ.size = μ.parts ⟨0, hN⟩ + ∑ j ∈ Finset.univ.filter (· ≠ ⟨0, hN⟩), μ.parts j := by
      simp only [size]
      rw [← Finset.add_sum_erase Finset.univ (fun j => μ.parts j) (Finset.mem_univ ⟨0, hN⟩)]
      congr 1
      apply Finset.sum_congr
      · ext x
        simp [Finset.mem_erase, Finset.mem_filter]
      · intro _ _; rfl
    rw [h] at hsum
    have : ∑ j ∈ Finset.univ.filter (· ≠ ⟨0, hN⟩), μ.parts j = 0 := by omega
    have hmem : i ∈ Finset.univ.filter (· ≠ (⟨0, hN⟩ : Fin N)) := by
      simp [Finset.mem_filter]
      intro heq
      simp only [Fin.ext_iff] at heq
      exact hi heq
    exact Finset.sum_eq_zero_iff.mp this i hmem
  · intro h
    simp only [size]
    rw [Finset.sum_eq_single ⟨0, hN⟩]
    · intro j _ hj
      apply h
      simp only [ne_eq, Fin.ext_iff] at hj
      exact hj
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- An N-partition with size 0 is the zero partition. -/
lemma eq_zero_of_size_eq_zero (μ : NPartition N) (h : μ.size = 0) : μ = 0 := by
  ext i
  simp only [zero_parts]
  have : μ.parts i ≤ μ.size := parts_le_size μ i
  omega

/-- An N-partition has size 0 if and only if it is the zero partition. -/
@[simp]
lemma size_eq_zero_iff (μ : NPartition N) : μ.size = 0 ↔ μ = 0 :=
  ⟨eq_zero_of_size_eq_zero μ, fun h => h ▸ zero_size⟩

/-- A non-zero N-partition has positive size. -/
lemma size_pos_of_ne_zero {μ : NPartition N} (h : μ ≠ 0) : 0 < μ.size := by
  rw [Nat.pos_iff_ne_zero]
  intro hsize
  exact h (size_eq_zero_iff μ |>.mp hsize)

/-- The size of a sum of N-partitions equals the sum of their sizes. -/
@[simp]
lemma add_size (μ ν : NPartition N) : (μ + ν).size = μ.size + ν.size := by
  simp only [size, add_parts]
  exact Finset.sum_add_distrib

@[simp]
lemma coe_parts (μ : NPartition N) : (μ : Fin N → ℕ) = μ.parts := rfl

/-- Alias for `le_def` matching SchurBasics.lean naming. -/
lemma le_iff {μ ν : NPartition N} : μ ≤ ν ↔ ∀ i, μ.parts i ≤ ν.parts i := Iff.rfl

/-- Membership in partitionsOfSize is characterized by size. -/
lemma mem_partitionsOfSize (μ : NPartition N) (n : ℕ) :
    μ ∈ partitionsOfSize n ↔ μ.size = n := by
  simp only [partitionsOfSize, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, Subtype.exists, exists_prop]
  constructor
  · rintro ⟨ν, hν, rfl⟩
    exact hν
  · intro hμ
    exact ⟨μ, hμ, rfl⟩

/-- The set of N-partitions with size n is finite (Set.Finite version). -/
lemma finite_of_size (n : ℕ) : Set.Finite { μ : NPartition N | μ.size = n } := by
  haveI : Fintype { μ : NPartition N // μ.size = n } := instFintypeSizeEq n
  have : Finite { μ : NPartition N // μ.size = n } := inferInstance
  exact Set.finite_coe_iff.mp this

/-- μ ≤ ν implies |μ| ≤ |ν| -/
lemma size_le_of_le {μ ν : NPartition N} (h : μ ≤ ν) : μ.size ≤ ν.size := by
  unfold size
  apply Finset.sum_le_sum
  intro i _
  exact h i

@[simp]
lemma zero_length : (0 : NPartition N).length = 0 := by
  simp only [length, zero_parts, ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty]

/-- An N-partition has length 0 if and only if it is the zero partition. -/
@[simp]
lemma length_eq_zero_iff {μ : NPartition N} : μ.length = 0 ↔ μ = 0 := by
  constructor
  · intro h
    simp only [length, Finset.card_eq_zero] at h
    have h' : ∀ i : Fin N, μ.parts i = 0 := by
      intro i
      by_contra hne
      have hmem : i ∈ Finset.univ.filter (fun j : Fin N => μ.parts j ≠ 0) := by
        simp [Finset.mem_filter, hne]
      simp [h] at hmem
    ext i
    simp only [zero_parts_apply]
    exact h' i
  · intro h
    rw [h]
    exact zero_length

/-- A nonzero N-partition has positive length. -/
lemma length_pos_of_ne_zero {μ : NPartition N} (h : μ ≠ 0) : 0 < μ.length := by
  rw [Nat.pos_iff_ne_zero]
  exact fun hz => h (length_eq_zero_iff.mp hz)


/-- The length is at most N. -/
lemma length_le (μ : NPartition N) : μ.length ≤ N := by
  simp only [length]
  calc (Finset.univ.filter (fun i : Fin N => μ.parts i ≠ 0)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = N := Finset.card_fin N

@[simp]
lemma mk'_parts (parts : Fin N → ℕ) (h : ∀ i j : Fin N, i ≤ j → parts j ≤ parts i) :
    (mk' parts h).parts = parts := rfl

@[simp]
lemma mk'_antitone (parts : Fin N → ℕ) (h : ∀ i j : Fin N, i ≤ j → parts j ≤ parts i) :
    (mk' parts h).antitone = h := rfl

@[simp]
lemma part_eq_parts (μ : NPartition N) (i : Fin N) : μ.part i = μ.parts i := rfl

/-- Alternative characterization: membership in terms of the row index -/
lemma mem_youngDiagram' {μ : NPartition N} {i : Fin N} {j : ℕ} :
    (i, j) ∈ μ.youngDiagram ↔ j < μ.parts i := mem_youngDiagram

/-- The Young diagram is empty iff the partition is zero.
    This follows from the definition: Y(λ) = {(i,j) | j < λ_i}, which is empty iff all λ_i = 0. -/
lemma youngDiagram_eq_empty_iff {μ : NPartition N} :
    μ.youngDiagram = ∅ ↔ μ = 0 := by
  constructor
  · intro h
    ext i
    by_contra hne
    have : (i, 0) ∈ μ.youngDiagram := by
      rw [mem_youngDiagram]
      exact Nat.pos_of_ne_zero hne
    rw [h] at this
    exact Finset.notMem_empty _ this
  · intro h
    rw [h]
    ext c
    simp only [mem_youngDiagram, zero_parts_apply, Nat.not_lt_zero, Finset.notMem_empty]

/-- The Young diagram is nonempty iff the partition is nonzero -/
lemma youngDiagram_nonempty_iff {μ : NPartition N} :
    μ.youngDiagram.Nonempty ↔ μ ≠ 0 := by
  rw [Finset.nonempty_iff_ne_empty, ne_eq, youngDiagram_eq_empty_iff]

/-- The row i of the Young diagram has exactly μ.parts i elements.
    This captures the definition that row i has λ_i boxes. -/
lemma youngDiagram_row_card (μ : NPartition N) (i : Fin N) :
    (μ.youngDiagram.filter fun c => c.1 = i).card = μ.parts i := by
  have h : μ.youngDiagram.filter (fun c => c.1 = i) =
           (Finset.range (μ.parts i)).map ⟨fun j => (i, j), fun _ _ h => congr_arg Prod.snd h⟩ := by
    ext c
    simp only [Finset.mem_filter, mem_youngDiagram, Finset.mem_map, Finset.mem_range,
               Function.Embedding.coeFn_mk]
    constructor
    · intro ⟨hj, hi⟩
      refine ⟨c.2, by rw [hi] at hj; exact hj, ?_⟩
      rw [Prod.mk.injEq]
      exact ⟨hi.symm, rfl⟩
    · intro ⟨j, hj, hc⟩
      rw [Prod.mk.injEq] at hc
      constructor
      · rw [← hc.1, ← hc.2]; exact hj
      · exact hc.1.symm
  rw [h, Finset.card_map, Finset.card_range]

/-- Cells in a Young diagram have bounded column indices -/
lemma youngDiagram_snd_lt_parts {μ : NPartition N} {c : Fin N × ℕ}
    (h : c ∈ μ.youngDiagram) : c.2 < μ.parts c.1 := mem_youngDiagram.mp h

/-- The Young diagram is bounded by the first row length (when N > 0).
    Since λ is weakly decreasing, all columns are at most λ_0. -/
lemma youngDiagram_subset_prod (μ : NPartition N) (hN : 0 < N) :
    μ.youngDiagram ⊆ Finset.univ ×ˢ Finset.range (μ.parts ⟨0, hN⟩) := by
  intro c hc
  rw [mem_youngDiagram] at hc
  simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
  calc c.2 < μ.parts c.1 := hc
    _ ≤ μ.parts ⟨0, hN⟩ := μ.antitone (Nat.zero_le _)

/-- Version of `youngDiagram_subset_prod` using `[NeZero N]` typeclass.
    Useful for code that already has `[NeZero N]` in scope. -/
lemma youngDiagram_subset_prod' {N : ℕ} [NeZero N] (μ : NPartition N) :
    μ.youngDiagram ⊆ Finset.univ ×ˢ Finset.range (μ.parts 0) := by
  intro c hc
  rw [mem_youngDiagram] at hc
  simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
  calc c.2 < μ.parts c.1 := hc
    _ ≤ μ.parts 0 := μ.antitone (Fin.zero_le _)

/-- The cell (i, 0) is in the Young diagram iff μ_i > 0.
    This characterizes which rows are nonempty. -/
lemma mem_youngDiagram_zero_col {μ : NPartition N} {i : Fin N} :
    (i, 0) ∈ μ.youngDiagram ↔ 0 < μ.parts i := by
  rw [mem_youngDiagram]

/-- The total number of cells in the Young diagram equals the size of the partition. -/
lemma youngDiagram_card (μ : NPartition N) : μ.youngDiagram.card = μ.size := by
  simp only [size]
  -- The Young diagram is the disjoint union of rows
  have hdisjoint : Set.PairwiseDisjoint (Finset.univ : Finset (Fin N))
      (fun i => (Finset.range (μ.parts i)).map ⟨fun j => (i, j), fun _ _ h => congr_arg Prod.snd h⟩) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_map, Finset.mem_range] at ha hb
    obtain ⟨_, _, rfl⟩ := ha
    obtain ⟨_, _, rfl⟩ := hb
    intro h
    exact hij (congr_arg Prod.fst h)
  rw [youngDiagram, Finset.card_biUnion hdisjoint]
  congr 1
  funext i
  simp only [Finset.card_map, Finset.card_range]

/-- The zero N-partition has empty Young diagram -/
@[simp]
lemma youngDiagram_zero : (0 : NPartition N).youngDiagram = ∅ := by
  ext c
  simp only [mem_youngDiagram, zero_parts_apply, Nat.not_lt_zero]
  simp

/-- μ ≤ ν is equivalent to Y(μ) ⊆ Y(ν).
    This is the key equivalence for partition containment. -/
lemma le_iff_youngDiagram_subset {μ ν : NPartition N} :
    μ ≤ ν ↔ μ.youngDiagram ⊆ ν.youngDiagram := by
  rw [le_iff]
  constructor
  · intro h c hc
    rw [mem_youngDiagram] at hc ⊢
    exact lt_of_lt_of_le hc (h c.1)
  · intro h i
    by_contra hne
    push_neg at hne
    have hmem : (i, ν.parts i) ∈ μ.youngDiagram := by
      rw [mem_youngDiagram]
      exact hne
    have hnotmem : (i, ν.parts i) ∉ ν.youngDiagram := by
      rw [mem_youngDiagram]
      exact Nat.lt_irrefl _
    exact hnotmem (h hmem)

/-- Alternative characterization: membership in terms of row index -/
lemma mem_skewYoungDiagram' {lam mu : NPartition N} {i : Fin N} {j : ℕ} :
    (i, j) ∈ skewYoungDiagram lam mu ↔ j ∈ Finset.Ico (mu.parts i) (lam.parts i) := by
  rw [mem_skewYoungDiagram, Finset.mem_Ico]

/-- The skew diagram Y(λ/λ) is empty. -/
@[simp]
lemma skewYoungDiagram_self (lam : NPartition N) :
    skewYoungDiagram lam lam = ∅ := by
  ext c
  rw [mem_skewYoungDiagram]
  simp only [Finset.notMem_empty, iff_false, not_and, not_lt]
  intro h
  exact h

/-- The skew diagram Y(λ/0) equals Y(λ). -/
@[simp]
lemma skewYoungDiagram_zero' (lam : NPartition N) :
    skewYoungDiagram lam 0 = lam.youngDiagram := by
  ext c
  simp only [mem_skewYoungDiagram, mem_youngDiagram, zero_parts_apply]
  constructor
  · intro ⟨_, h⟩; exact h
  · intro h; exact ⟨Nat.zero_le _, h⟩

/-- The skew diagram is contained in the larger Young diagram. -/
lemma skewYoungDiagram_subset_youngDiagram (lam mu : NPartition N) :
    skewYoungDiagram lam mu ⊆ lam.youngDiagram := by
  intro c hc
  rw [mem_skewYoungDiagram] at hc
  rw [mem_youngDiagram]
  exact hc.2

/-- The cardinality of a skew Young diagram. -/
lemma skewYoungDiagram_card (lam mu : NPartition N) :
    (skewYoungDiagram lam mu).card = ∑ i, (lam.parts i - mu.parts i) := by
  simp only [skewYoungDiagram]
  -- Use the fact that Y(λ) \ Y(μ) partitions into rows
  have h : lam.youngDiagram \ mu.youngDiagram =
      Finset.univ.biUnion fun i =>
        (Finset.Ico (mu.parts i) (lam.parts i)).map
          ⟨fun j => (i, j), fun _ _ h => congr_arg Prod.snd h⟩ := by
    ext c
    simp only [Finset.mem_sdiff, mem_youngDiagram, Finset.mem_biUnion, Finset.mem_univ,
               true_and, Finset.mem_map, Finset.mem_Ico, Function.Embedding.coeFn_mk]
    constructor
    · intro ⟨hlt, hnotmem⟩
      refine ⟨c.1, c.2, ?_, rfl⟩
      exact ⟨Nat.not_lt.mp hnotmem, hlt⟩
    · intro ⟨i, j, ⟨hle, hlt⟩, heq⟩
      rw [← heq]
      exact ⟨hlt, Nat.not_lt.mpr hle⟩
  rw [h]
  have hdisjoint : Set.PairwiseDisjoint (Finset.univ : Finset (Fin N))
      (fun i => (Finset.Ico (mu.parts i) (lam.parts i)).map
        ⟨fun j => (i, j), fun _ _ h => congr_arg Prod.snd h⟩) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_map, Finset.mem_Ico] at ha hb
    obtain ⟨_, _, rfl⟩ := ha
    obtain ⟨_, _, rfl⟩ := hb
    intro h
    exact hij (congr_arg Prod.fst h)
  rw [Finset.card_biUnion hdisjoint]
  congr 1
  funext i
  simp only [Finset.card_map, Nat.card_Ico]

/-- The skew diagram is empty iff λ ≤ μ componentwise. -/
lemma skewYoungDiagram_eq_empty_iff {lam mu : NPartition N} :
    skewYoungDiagram lam mu = ∅ ↔ ∀ i, lam.parts i ≤ mu.parts i := by
  constructor
  · intro h i
    by_contra hne
    push_neg at hne
    have : (i, mu.parts i) ∈ skewYoungDiagram lam mu := by
      rw [mem_skewYoungDiagram]
      exact ⟨le_refl _, hne⟩
    rw [h] at this
    exact Finset.notMem_empty _ this
  · intro h
    ext c
    simp only [Finset.notMem_empty, iff_false]
    rw [mem_skewYoungDiagram]
    intro ⟨hle, hlt⟩
    have := h c.1
    omega

/-- The row partition has size n. -/
@[simp]
lemma rowPartition_size (N : ℕ) (n : ℕ) (hN : 0 < N) :
    (rowPartition N n hN).size = n := by
  simp only [rowPartition, size]
  rw [Finset.sum_eq_single ⟨0, hN⟩]
  · simp
  · intro b _ hb
    simp only [ite_eq_right_iff]
    intro h
    exact (hb (Fin.ext h)).elim
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The first part of the row partition is n. -/
@[simp]
lemma rowPartition_parts_zero (N : ℕ) (n : ℕ) (hN : 0 < N) :
    (rowPartition N n hN).parts ⟨0, hN⟩ = n := by simp [rowPartition]

/-- All other parts of the row partition are 0. -/
@[simp]
lemma rowPartition_parts_pos (N : ℕ) (n : ℕ) (hN : 0 < N) (i : Fin N) (hi : 0 < i.val) :
    (rowPartition N n hN).parts i = 0 := by
  simp only [rowPartition]
  simp only [ite_eq_right_iff]
  omega

/-- The cardinality of elements of `Fin N` with value less than `n` is `n` (when `n ≤ N`).
    This is a specialized form of `Fin.card_filter_val_lt` for the case when `n ≤ N`.

    Used for proving properties of `colPartition`. -/
lemma card_filter_fin_val_lt (N n : ℕ) (hn : n ≤ N) :
    (Finset.univ.filter (fun i : Fin N => i.val < n)).card = n := by
  have h := @Fin.card_filter_val_lt N n
  simp only [min_eq_right hn] at h
  exact h

/-- The sum of indicators `if i.val < n then 1 else 0` over `Fin N` equals `n` (when `n ≤ N`).

    Used for proving properties of `colPartition`. -/
lemma sum_ite_fin_val_lt_eq (N n : ℕ) (hn : n ≤ N) :
    (∑ i : Fin N, if i.val < n then 1 else 0) = n := by
  have h1 : (∑ i : Fin N, if i.val < n then 1 else 0) =
            (Finset.univ.filter (fun i : Fin N => i.val < n)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [h1]
  exact card_filter_fin_val_lt N n hn

/-- The column partition has size n. -/
@[simp]
lemma colPartition_size (N : ℕ) (n : ℕ) (hn : n ≤ N) :
    (colPartition N n hn).size = n := by
  simp only [colPartition, size]
  exact sum_ite_fin_val_lt_eq N n hn

/-- The first n parts of the column partition are 1. -/
@[simp]
lemma colPartition_parts_lt (N : ℕ) (n : ℕ) (hn : n ≤ N) (i : Fin N) (hi : i.val < n) :
    (colPartition N n hn).parts i = 1 := by simp [colPartition, hi]

/-- Parts beyond n in the column partition are 0. -/
@[simp]
lemma colPartition_parts_ge (N : ℕ) (n : ℕ) (hn : n ≤ N) (i : Fin N) (hi : n ≤ i.val) :
    (colPartition N n hn).parts i = 0 := by simp [colPartition, Nat.not_lt.mpr hi]

/-- The zero partition is its own transpose. -/
lemma zero_isTranspose : IsTranspose (fun _ : Fin N => 0) (fun _ : Fin N => 0) := by
  constructor
  · intro i
    have h : (Finset.univ.filter fun j : Fin N => i.val + 1 ≤ (0 : ℕ)) = ∅ := by
      simp only [Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
      intro j
      exact Nat.not_succ_le_zero _
    rw [h]
    simp
  · intro j
    have h : (Finset.univ.filter fun i : Fin N => j.val + 1 ≤ (0 : ℕ)) = ∅ := by
      simp only [Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
      intro i
      exact Nat.not_succ_le_zero _
    rw [h]
    simp

end NPartition
end


/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_isNPartition_iff_antitone
  {lam : Fin N → ℕ} :
-- imply
  IsNPartition lam ↔ Antitone lam := by
-- proof
  apply _root_.isNPartition_iff_antitone

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_isNPartition_zero :
-- imply
  IsNPartition (0 : Fin N → ℕ) := by
-- proof
  apply _root_.isNPartition_zero

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma add
  {α β : Fin N → ℕ}
-- given
  (hα : IsNPartition α)
  (hβ : IsNPartition β) :
-- imply
  IsNPartition (α + β) := by
-- proof
  apply _root_.IsNPartition.add hα hβ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_monotone
-- given
  (μ : NPartition N) :
-- imply
  ∀ i j : Fin N, i ≤ j → μ.parts j ≤ μ.parts i := by
-- proof
  apply NPartition.monotone μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_weaklyDecreasing
-- given
  (μ : NPartition N) :
-- imply
  ∀ i j : Fin N, i ≤ j → μ.parts j ≤ μ.parts i := by
-- proof
  apply NPartition.weaklyDecreasing μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_parts_antitone
-- given
  (μ : NPartition N) :
-- imply
  Antitone μ.parts := by
-- proof
  apply NPartition.parts_antitone μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_isNPartition
-- given
  (μ : NPartition N) :
-- imply
  IsNPartition μ.parts := by
-- proof
  apply NPartition.isNPartition μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_ext
  {μ ν : NPartition N}
-- given
  (h : μ.parts = ν.parts) :
-- imply
  μ = ν := by
-- proof
  apply NPartition.ext h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma ext'
  {μ ν : NPartition N} :
-- imply
  μ = ν ↔ ∀ i, μ.parts i = ν.parts i := by
-- proof
  apply NPartition.ext'

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_ext_parts
  {μ ν : NPartition N}
-- given
  (h : ∀ i, μ.parts i = ν.parts i) :
-- imply
  μ = ν := by
-- proof
  apply NPartition.ext_parts h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_parts_ext_iff
  {μ ν : NPartition N} :
-- imply
  μ = ν ↔ μ.parts = ν.parts := by
-- proof
  apply NPartition.parts_ext_iff

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_zero_parts :
-- imply
  (0 : NPartition N).parts = fun _ => 0 := by
-- proof
  apply NPartition.zero_parts

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma zero_parts_apply
-- given
  (i : Fin N) :
-- imply
  (0 : NPartition N).parts i = 0 := by
-- proof
  apply NPartition.zero_parts_apply i

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_size_eq_sum
-- given
  (μ : NPartition N) :
-- imply
  μ.size = ∑ i, μ.parts i := by
-- proof
  apply NPartition.size_eq_sum μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_zero_size :
-- imply
  (0 : NPartition N).size = 0 := by
-- proof
  apply NPartition.zero_size

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma parts_le_size
-- given
  (μ : NPartition N)
  (i : Fin N) :
-- imply
  μ.parts i ≤ μ.size := by
-- proof
  apply NPartition.parts_le_size μ i

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_parts_zero_max
-- given
  (hN : 0 < N)
  (μ : NPartition N)
  (i : Fin N) :
-- imply
  μ.parts i ≤ μ.parts ⟨0, hN⟩ := by
-- proof
  apply NPartition.parts_zero_max μ i hN

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_parts_zero_eq_size_iff
-- given
  (hN : 0 < N)
  (μ : NPartition N) :
-- imply
  μ.parts ⟨0, hN⟩ = μ.size ↔ ∀ i : Fin N, i.val ≠ 0 → μ.parts i = 0 := by
-- proof
  apply NPartition.parts_zero_eq_size_iff μ hN

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_eq_zero_of_size_eq_zero
-- given
  (μ : NPartition N)
  (h : μ.size = 0) :
-- imply
  μ = 0 := by
-- proof
  apply NPartition.eq_zero_of_size_eq_zero μ h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_size_eq_zero_iff
-- given
  (μ : NPartition N) :
-- imply
  μ.size = 0 ↔ μ = 0 := by
-- proof
  apply NPartition.size_eq_zero_iff μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_size_pos_of_ne_zero
  {μ : NPartition N}
-- given
  (h : μ ≠ 0) :
-- imply
  0 < μ.size := by
-- proof
  apply NPartition.size_pos_of_ne_zero h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma add_parts
-- given
  (μ ν : NPartition N)
  (i : Fin N) :
-- imply
  (μ + ν).parts i = μ.parts i + ν.parts i := by
-- proof
  apply NPartition.add_parts μ ν i

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_add_size
-- given
  (μ ν : NPartition N) :
-- imply
  (μ + ν).size = μ.size + ν.size := by
-- proof
  apply NPartition.add_size μ ν

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_add_comm
-- given
  (μ ν : NPartition N) :
-- imply
  μ + ν = ν + μ := by
-- proof
  apply NPartition.add_comm μ ν

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_add_zero
-- given
  (μ : NPartition N) :
-- imply
  μ + 0 = μ := by
-- proof
  apply NPartition.add_zero μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_zero_add
-- given
  (μ : NPartition N) :
-- imply
  0 + μ = μ := by
-- proof
  apply NPartition.zero_add μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_add_assoc
-- given
  (μ ν ρ : NPartition N) :
-- imply
  μ + ν + ρ = μ + (ν + ρ) := by
-- proof
  apply NPartition.add_assoc μ ν ρ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_coe_parts
-- given
  (μ : NPartition N) :
-- imply
  (μ : Fin N → ℕ) = μ.parts := by
-- proof
  apply NPartition.coe_parts μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_le_def
-- given
  (μ ν : NPartition N) :
-- imply
  μ ≤ ν ↔ ∀ i, μ.parts i ≤ ν.parts i := by
-- proof
  apply NPartition.le_def μ ν

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_le_iff
  {μ ν : NPartition N} :
-- imply
  μ ≤ ν ↔ ∀ i, μ.parts i ≤ ν.parts i := by
-- proof
  apply NPartition.le_iff

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_mem_partitionsOfSize
-- given
  (μ : NPartition N)
  (n : ℕ) :
-- imply
  μ ∈ partitionsOfSize n ↔ μ.size = n := by
-- proof
  apply NPartition.mem_partitionsOfSize μ n

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_finite_of_size
-- given
  (n : ℕ) :
-- imply
  Set.Finite { μ : NPartition N | μ.size = n } := by
-- proof
  apply NPartition.finite_of_size n

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_zero_le
-- given
  (μ : NPartition N) :
-- imply
  (0 : NPartition N) ≤ μ := by
-- proof
  apply NPartition.zero_le μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_size_le_of_le
  {μ ν : NPartition N}
-- given
  (h : μ ≤ ν) :
-- imply
  μ.size ≤ ν.size := by
-- proof
  apply NPartition.size_le_of_le h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_zero_length :
-- imply
  (0 : NPartition N).length = 0 := by
-- proof
  apply NPartition.zero_length

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_length_eq_zero_iff
  {μ : NPartition N} :
-- imply
  μ.length = 0 ↔ μ = 0 := by
-- proof
  apply NPartition.length_eq_zero_iff

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_length_pos_of_ne_zero
  {μ : NPartition N}
-- given
  (h : μ ≠ 0) :
-- imply
  0 < μ.length := by
-- proof
  apply NPartition.length_pos_of_ne_zero h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_length_le
-- given
  (μ : NPartition N) :
-- imply
  μ.length ≤ N := by
-- proof
  apply NPartition.length_le μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_finite_support
-- given
  (μ : NPartition N) :
-- imply
  Set.Finite {i | μ.parts i ≠ 0} := by
-- proof
  apply NPartition.finite_support μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_mk'_parts
-- given
  (parts : Fin N → ℕ)
  (h : ∀ i j : Fin N, i ≤ j → parts j ≤ parts i) :
-- imply
  (mk' parts h).parts = parts := by
-- proof
  apply NPartition.mk'_parts parts h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_mk'_antitone
-- given
  (parts : Fin N → ℕ)
  (h : ∀ i j : Fin N, i ≤ j → parts j ≤ parts i) :
-- imply
  (mk' parts h).antitone = h := by
-- proof
  apply NPartition.mk'_antitone parts h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_part_eq_parts
-- given
  (μ : NPartition N)
  (i : Fin N) :
-- imply
  μ.part i = μ.parts i := by
-- proof
  apply NPartition.part_eq_parts μ i

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_ofPartition_size
  {n : ℕ}
-- given
  (p : Nat.Partition n)
  (hp : Multiset.card p.parts ≤ N) :
-- imply
  (ofPartition p hp).size = n := by
-- proof
  apply NPartition.ofPartition_size p hp

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_toPartition_card_le
-- given
  (μ : NPartition N) :
-- imply
  Multiset.card μ.toPartition.parts ≤ N := by
-- proof
  apply NPartition.toPartition_card_le μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma mem_youngDiagram
  {μ : NPartition N}
  {c : Fin N × ℕ} :
-- imply
  c ∈ μ.youngDiagram ↔ c.2 < μ.parts c.1 := by
-- proof
  apply NPartition.mem_youngDiagram

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_mem_youngDiagram'
  {μ : NPartition N}
  {i : Fin N}
  {j : ℕ} :
-- imply
  (i, j) ∈ μ.youngDiagram ↔ j < μ.parts i := by
-- proof
  apply NPartition.mem_youngDiagram'

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_youngDiagram_eq_empty_iff
  {μ : NPartition N} :
-- imply
  μ.youngDiagram = ∅ ↔ μ = 0 := by
-- proof
  apply NPartition.youngDiagram_eq_empty_iff

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_youngDiagram_nonempty_iff
  {μ : NPartition N} :
-- imply
  μ.youngDiagram.Nonempty ↔ μ ≠ 0 := by
-- proof
  apply NPartition.youngDiagram_nonempty_iff

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_youngDiagram_row_card
-- given
  (μ : NPartition N)
  (i : Fin N) :
-- imply
  (μ.youngDiagram.filter fun c => c.1 = i).card = μ.parts i := by
-- proof
  apply NPartition.youngDiagram_row_card μ i

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_youngDiagram_snd_lt_parts
  {μ : NPartition N}
  {c : Fin N × ℕ}
-- given
  (h : c ∈ μ.youngDiagram) :
-- imply
  c.2 < μ.parts c.1 := by
-- proof
  apply NPartition.youngDiagram_snd_lt_parts h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_youngDiagram_subset_prod
-- given
  (hN : 0 < N)
  (μ : NPartition N) :
-- imply
  μ.youngDiagram ⊆ Finset.univ ×ˢ Finset.range (μ.parts ⟨0, hN⟩) := by
-- proof
  apply NPartition.youngDiagram_subset_prod μ hN

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_youngDiagram_subset_prod'
  {N : ℕ} [NeZero N]
-- given
  (μ : NPartition N) :
-- imply
  μ.youngDiagram ⊆ Finset.univ ×ˢ Finset.range (μ.parts 0) := by
-- proof
  apply NPartition.youngDiagram_subset_prod' μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_mem_youngDiagram_zero_col
  {μ : NPartition N}
  {i : Fin N} :
-- imply
  (i, 0) ∈ μ.youngDiagram ↔ 0 < μ.parts i := by
-- proof
  apply NPartition.mem_youngDiagram_zero_col

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_youngDiagram_card
-- given
  (μ : NPartition N) :
-- imply
  μ.youngDiagram.card = μ.size := by
-- proof
  apply NPartition.youngDiagram_card μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_youngDiagram_zero :
-- imply
  (0 : NPartition N).youngDiagram = ∅ := by
-- proof
  apply NPartition.youngDiagram_zero

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_le_iff_youngDiagram_subset
  {μ ν : NPartition N} :
-- imply
  μ ≤ ν ↔ μ.youngDiagram ⊆ ν.youngDiagram := by
-- proof
  apply NPartition.le_iff_youngDiagram_subset

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma mem_skewYoungDiagram
  {lam mu : NPartition N}
  {c : Fin N × ℕ} :
-- imply
  c ∈ skewYoungDiagram lam mu ↔ mu.parts c.1 ≤ c.2 ∧ c.2 < lam.parts c.1 := by
-- proof
  apply NPartition.mem_skewYoungDiagram

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_mem_skewYoungDiagram'
  {lam mu : NPartition N}
  {i : Fin N}
  {j : ℕ} :
-- imply
  (i, j) ∈ skewYoungDiagram lam mu ↔ j ∈ Finset.Ico (mu.parts i) (lam.parts i) := by
-- proof
  apply NPartition.mem_skewYoungDiagram'

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_skewYoungDiagram_self
-- given
  (lam : NPartition N) :
-- imply
  skewYoungDiagram lam lam = ∅ := by
-- proof
  apply NPartition.skewYoungDiagram_self lam

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_skewYoungDiagram_zero'
-- given
  (lam : NPartition N) :
-- imply
  skewYoungDiagram lam 0 = lam.youngDiagram := by
-- proof
  apply NPartition.skewYoungDiagram_zero' lam

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_skewYoungDiagram_subset_youngDiagram
-- given
  (lam mu : NPartition N) :
-- imply
  skewYoungDiagram lam mu ⊆ lam.youngDiagram := by
-- proof
  apply NPartition.skewYoungDiagram_subset_youngDiagram lam mu

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_skewYoungDiagram_card
-- given
  (lam mu : NPartition N) :
-- imply
  (skewYoungDiagram lam mu).card = ∑ i, (lam.parts i - mu.parts i) := by
-- proof
  apply NPartition.skewYoungDiagram_card lam mu

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_skewYoungDiagram_eq_empty_iff
  {lam mu : NPartition N} :
-- imply
  skewYoungDiagram lam mu = ∅ ↔ ∀ i, lam.parts i ≤ mu.parts i := by
-- proof
  apply NPartition.skewYoungDiagram_eq_empty_iff

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_rowPartition_size
-- given
  (N : ℕ)
  (hN : 0 < N)
  (n : ℕ) :
-- imply
  (rowPartition N n hN).size = n := by
-- proof
  apply NPartition.rowPartition_size N n hN

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_rowPartition_parts_zero
-- given
  (N : ℕ)
  (hN : 0 < N)
  (n : ℕ) :
-- imply
  (rowPartition N n hN).parts ⟨0, hN⟩ = n := by
-- proof
  apply NPartition.rowPartition_parts_zero N n hN

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_rowPartition_parts_pos
-- given
  (N : ℕ)
  (i : Fin N)
  (hN : 0 < N)
  (hi : 0 < i.val)
  (n : ℕ) :
-- imply
  (rowPartition N n hN).parts i = 0 := by
-- proof
  apply NPartition.rowPartition_parts_pos N n hN i hi

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_card_filter_fin_val_lt
-- given
  (N n : ℕ)
  (hn : n ≤ N) :
-- imply
  (Finset.univ.filter (fun i : Fin N => i.val < n)).card = n := by
-- proof
  apply NPartition.card_filter_fin_val_lt N n hn

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_sum_ite_fin_val_lt_eq
-- given
  (N n : ℕ)
  (hn : n ≤ N) :
-- imply
  (∑ i : Fin N, if i.val < n then 1 else 0) = n := by
-- proof
  apply NPartition.sum_ite_fin_val_lt_eq N n hn

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_colPartition_size
-- given
  (N n : ℕ)
  (hn : n ≤ N) :
-- imply
  (colPartition N n hn).size = n := by
-- proof
  apply NPartition.colPartition_size N n hn

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_colPartition_parts_lt
-- given
  (N n : ℕ)
  (i : Fin N)
  (hn : n ≤ N)
  (hi : i.val < n) :
-- imply
  (colPartition N n hn).parts i = 1 := by
-- proof
  apply NPartition.colPartition_parts_lt N n hn i hi

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_colPartition_parts_ge
-- given
  (N n : ℕ)
  (i : Fin N)
  (hn : n ≤ N)
  (hi : n ≤ i.val) :
-- imply
  (colPartition N n hn).parts i = 0 := by
-- proof
  apply NPartition.colPartition_parts_ge N n hn i hi

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_zero_isTranspose :
-- imply
  IsTranspose (fun _ : Fin N => 0) (fun _ : Fin N => 0) := by
-- proof
  apply NPartition.zero_isTranspose

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma pv_filter_ne_zero_sum
-- given
  (m : Multiset ℕ) :
-- imply
  (m.filter (· ≠ 0)).sum = m.sum := by
-- proof
  apply NPartition.filter_ne_zero_sum m


-- created on 2026-10-20
-- updated on 2026-10-23
