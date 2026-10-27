import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Young.PieriJacobiTrudi.Part32
import Lemma.Matrix.LGV2
import Lemma.MvPolynomial.OmegaInvolution
import Lemma.Partition.NPartition
import Lemma.MvPolynomial.LittlewoodRichardson
open SymmetricFunctions
open SymmetricFunctions.NPartition
open SymmetricFunctions.SkewPartition
open Finset
open Matrix
open MvPolynomial hiding R
open scoped BigOperators Classical


section
-- ac-theorems


open Finset BigOperators Matrix MvPolynomial

namespace SymmetricFunctions

variable {N : ℕ} {R : Type*} [CommRing R]

namespace NPartition

variable {N : ℕ}

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


/-- Double counting lemma: summing cardinalities of filter sets over rows equals
    summing over columns. This is used to prove that transpose preserves size. -/
lemma sum_card_filter_eq_sum_card_filter {M : ℕ} (P : Fin N → Fin M → Prop)
    [∀ i j, Decidable (P i j)] :
    ∑ i : Fin N, (Finset.univ.filter fun j : Fin M => P i j).card =
    ∑ j : Fin M, (Finset.univ.filter fun i : Fin N => P i j).card := by
  have h1 : ∀ i : Fin N, (Finset.univ.filter fun j : Fin M => P i j).card =
      ∑ j : Fin M, if P i j then 1 else 0 := fun i => by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have h2 : ∀ j : Fin M, (Finset.univ.filter fun i : Fin N => P i j).card =
      ∑ i : Fin N, if P i j then 1 else 0 := fun j => by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [h1, h2]
  rw [Finset.sum_comm]

/-- Helper: cardinality of {r : Fin N | r ≤ i} equals i.val + 1. -/
lemma card_filter_le_fin (i : Fin N) :
    (Finset.univ.filter fun r : Fin N => r ≤ i).card = i.val + 1 := by
  have h : (Finset.univ.filter fun r : Fin N => r ≤ i) = Finset.Iic i := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
  rw [h, Fin.card_Iic]

/-- The transpose box equivalence: for weakly decreasing partitions λ and λᵗ
    satisfying the transpose property, box (i, j) is in λ iff (j, i) is in λᵗ.

    This is the key lemma that relates the two counting conditions:
    j + 1 ≤ λ_i ↔ i + 1 ≤ λᵗ_j

    The proof uses the weakly decreasing property: if j + 1 ≤ λ_i, then all
    rows 0, 1, ..., i have at least j + 1 boxes, so λᵗ_j ≥ i + 1. -/
lemma IsTranspose.box_equiv {M : ℕ} {lam : Fin N → ℕ} {lamt : Fin M → ℕ}
    (hlam_mono : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hlamt_mono : ∀ i j : Fin M, i ≤ j → lamt j ≤ lamt i)
    (htranspose : IsTranspose lam lamt)
    (i : Fin N) (j : Fin M) :
    j.val + 1 ≤ lam i ↔ i.val + 1 ≤ lamt j := by
  constructor
  · intro h
    rw [htranspose.1 j]
    have h_subset : (Finset.univ.filter fun r : Fin N => r ≤ i) ⊆
                    (Finset.univ.filter fun r : Fin N => j.val + 1 ≤ lam r) := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact le_trans h (hlam_mono r i hr)
    calc i.val + 1 = (Finset.univ.filter fun r : Fin N => r ≤ i).card := (card_filter_le_fin i).symm
      _ ≤ (Finset.univ.filter fun r : Fin N => j.val + 1 ≤ lam r).card := Finset.card_le_card h_subset
  · intro h
    rw [htranspose.2 i]
    have h_subset : (Finset.univ.filter fun c : Fin M => c ≤ j) ⊆
                    (Finset.univ.filter fun c : Fin M => i.val + 1 ≤ lamt c) := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact le_trans h (hlamt_mono c j hc)
    calc j.val + 1 = (Finset.univ.filter fun c : Fin M => c ≤ j).card := (card_filter_le_fin j).symm
      _ ≤ (Finset.univ.filter fun c : Fin M => i.val + 1 ≤ lamt c).card := Finset.card_le_card h_subset

/-- The transpose of a partition preserves the sum of parts (number of boxes).

    This is a fundamental property of Young tableau transposition:
    |λ| = |λᵗ| (the size of the partition equals the size of its transpose).

    The proof uses double counting: both ∑ᵢ λᵢ and ∑ⱼ λᵗⱼ count the total
    number of boxes in the Young diagram, just organized differently. -/
lemma IsTranspose.sum_eq {M : ℕ} {lam : Fin N → ℕ} {lamt : Fin M → ℕ}
    (hlam_mono : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hlamt_mono : ∀ i j : Fin M, i ≤ j → lamt j ≤ lamt i)
    (htranspose : IsTranspose lam lamt) :
    ∑ i : Fin N, lam i = ∑ j : Fin M, lamt j := by
  -- Use htranspose to rewrite both sides
  have h_lhs : ∑ i : Fin N, lam i =
      ∑ i : Fin N, (Finset.univ.filter fun j : Fin M => i.val + 1 ≤ lamt j).card := by
    apply Finset.sum_congr rfl
    intro i _
    exact htranspose.2 i
  have h_rhs : ∑ j : Fin M, lamt j =
      ∑ j : Fin M, (Finset.univ.filter fun i : Fin N => j.val + 1 ≤ lam i).card := by
    apply Finset.sum_congr rfl
    intro j _
    exact htranspose.1 j
  rw [h_lhs, h_rhs]
  -- The key: use box_equiv to show the predicates are equivalent
  have h_equiv : ∀ i j, (i.val + 1 ≤ lamt j) ↔ (j.val + 1 ≤ lam i) := fun i j =>
    (htranspose.box_equiv hlam_mono hlamt_mono i j).symm
  -- Rewrite LHS using the equivalence
  have h_filter_eq : ∀ i : Fin N,
      (Finset.univ.filter fun j : Fin M => i.val + 1 ≤ lamt j) =
      (Finset.univ.filter fun j : Fin M => j.val + 1 ≤ lam i) := fun i => by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h_equiv i j
  simp_rw [h_filter_eq]
  exact sum_card_filter_eq_sum_card_filter (fun i j => j.val + 1 ≤ lam i)

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

/-- The column partition has size n. -/
@[simp]
lemma colPartition_size (N : ℕ) (n : ℕ) (hn : n ≤ N) :
    (colPartition N n hn).size = n := by
  simp only [colPartition, size]
  exact _root_.NPartition.sum_ite_fin_val_lt_eq N n hn

/-- The first n parts of the column partition are 1. -/
@[simp]
lemma colPartition_parts_lt (N : ℕ) (n : ℕ) (hn : n ≤ N) (i : Fin N) (hi : i.val < n) :
    (colPartition N n hn).parts i = 1 := by simp [colPartition, hi]

/-- Parts beyond n in the column partition are 0. -/
@[simp]
lemma colPartition_parts_ge (N : ℕ) (n : ℕ) (hn : n ≤ N) (i : Fin N) (hi : n ≤ i.val) :
    (colPartition N n hn).parts i = 0 := by simp [colPartition, Nat.not_lt.mpr hi]

end NPartition


section NPartitionEquiv

variable {N : ℕ}

/-- Converting to shared preserves parts. -/
@[simp]
lemma NPartition.toShared_parts (μ : NPartition N) :
    (NPartition.toShared μ).parts = μ.parts := rfl

/-- Converting from shared preserves parts. -/
@[simp]
lemma NPartition.ofShared_parts (μ : _root_.NPartition N) :
    (NPartition.ofShared μ).parts = μ.parts := rfl

/-- Converting to shared preserves size. -/
@[simp]
lemma NPartition.toShared_size (μ : NPartition N) :
    (NPartition.toShared μ).size = μ.size := rfl

/-- Converting from shared preserves size. -/
@[simp]
lemma NPartition.ofShared_size (μ : _root_.NPartition N) :
    (NPartition.ofShared μ).size = μ.size := rfl

/-- The zero partitions correspond under the equivalence. -/
@[simp]
lemma NPartition.toShared_zero : NPartition.toShared (0 : NPartition N) = 0 := by
  ext i; rfl

/-- The zero partitions correspond under the equivalence. -/
@[simp]
lemma NPartition.ofShared_zero : NPartition.ofShared (0 : _root_.NPartition N) = 0 := by
  ext i; rfl

/-- The equivalence preserves the LE relation. -/
lemma NPartition.toShared_le_iff (μ ν : NPartition N) :
    NPartition.toShared μ ≤ NPartition.toShared ν ↔ μ ≤ ν := by
  simp only [_root_.NPartition.le_def, NPartition.le_def, NPartition.toShared_parts]

/-- The equivalence preserves the LE relation. -/
lemma NPartition.ofShared_le_iff (μ ν : _root_.NPartition N) :
    NPartition.ofShared μ ≤ NPartition.ofShared ν ↔ μ ≤ ν := by
  simp only [_root_.NPartition.le_def, NPartition.le_def, NPartition.ofShared_parts]

end NPartitionEquiv


section TransposeBridge

variable {N : ℕ}

/-- The transpose of the local `SymmetricFunctions.NPartition` equals the transpose of
    the shared `_root_.NPartition` (via the `toShared`/`ofShared` equivalence).

    This is the bridge lemma connecting the two transpose definitions.
    Since both definitions compute (λᵗ)ᵢ = |{j : λⱼ ≥ i+1}|, they are definitionally equal
    when the parts are the same. -/
lemma NPartition.transpose_toShared_eq (lam : NPartition N) (hN : 0 < N) :
    (lam.transpose hN).toShared = (lam.toShared).transpose hN := by
  ext i
  rfl

/-- The transpose of a shared `_root_.NPartition` converted to local equals the local
    transpose of the converted partition.

    This is the inverse direction of the bridge lemma. -/
lemma NPartition.ofShared_transpose_eq (lam : _root_.NPartition N) (hN : 0 < N) :
    NPartition.ofShared (lam.transpose hN) = (NPartition.ofShared lam).transpose hN := by
  ext i
  rfl

/-- The transpose commutes with the equivalence. -/
lemma NPartition.equivShared_transpose (lam : NPartition N) (hN : 0 < N) :
    NPartition.equivShared (lam.transpose hN) =
      (NPartition.equivShared lam).transpose hN :=
  NPartition.transpose_toShared_eq lam hN

end TransposeBridge


section SymSSYTHelpers

variable {N : ℕ}

/-- Product over a multiset equals product over its sorted list.
    Since sorting preserves the multiset, the products are equal. -/
lemma multiset_prod_eq_sorted_prod {α : Type*} [LinearOrder α] {β : Type*} [CommMonoid β]
    (m : Multiset α) (f : α → β) :
    (m.map f).prod = ((m.sort (· ≤ ·)).map f).prod := by
  have h : (m.sort (· ≤ ·) : Multiset α) = m := Multiset.sort_eq m (· ≤ ·)
  conv_lhs => rw [← h]
  rfl

/-- Product over a list equals product over Fin indices.
    This converts a list product to a fintype product. -/
lemma list_prod_map_eq_fin_prod {α : Type*} {β : Type*} [CommMonoid β]
    (L : List α) (f : α → β) :
    (L.map f).prod = ∏ j : Fin L.length, f (L.get j) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [Fin.prod_univ_succ]
    conv_lhs => rw [ih]
    rfl

/-- The monomial from a Sym equals the product over its weakly increasing representation.
    This is a key lemma for connecting h_n to Schur polynomials. -/
lemma sym_monomial_eq_weaklyIncreasing_prod {R : Type*} [CommRing R] (n : ℕ) (s : Sym (Fin N) n) :
    (s.1.map (MvPolynomial.X (R := R))).prod =
    ∏ j : Fin n, MvPolynomial.X ((symToWeaklyIncreasing n s).val j) := by
  rw [multiset_prod_eq_sorted_prod]
  rw [list_prod_map_eq_fin_prod]
  have hlen : (s.1.sort (· ≤ ·)).length = n := by rw [Multiset.length_sort]; exact s.2
  apply Finset.prod_equiv (finCongr hlen)
  · intro i
    exact ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩
  · intro j _
    rw [List.get_eq_getElem]
    congr 1

/-- The round-trip from Sym to weakly increasing and back gives the same Sym.
    This shows that symToWeaklyIncreasing and weaklyIncreasingToSym form a bijection. -/
lemma weaklyIncreasingToSym_symToWeaklyIncreasing (n : ℕ) (s : Sym (Fin N) n) :
    weaklyIncreasingToSym n (symToWeaklyIncreasing n s).val = s := by
  unfold weaklyIncreasingToSym symToWeaklyIncreasing
  congr 1
  have hlen : (s.1.sort (· ≤ ·)).length = n := by rw [Multiset.length_sort]; exact s.2
  -- Show the lists are equal as multisets
  have h1 : ((List.finRange n).map (fun i => (s.1.sort (· ≤ ·)).get ⟨i.val, by rw [hlen]; exact i.isLt⟩)) =
            s.1.sort (· ≤ ·) := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_finRange, hlen]
    · intro i hi1 hi2
      simp only [List.getElem_map, List.getElem_finRange, List.get_eq_getElem]
      simp only [Fin.cast, Fin.val_mk]
  simp only [h1]
  exact Multiset.sort_eq s.1 (· ≤ ·)

/-- Sorting a weakly increasing list gives back the same list.
    This is key for the surjectivity of symToRowSSYT. -/
lemma sort_weaklyIncreasing_list_eq {n : ℕ} (f : Fin n → Fin N)
    (hf : ∀ i j, i ≤ j → f i ≤ f j) :
    ((Multiset.ofList ((List.finRange n).map f)).sort (· ≤ ·)) = (List.finRange n).map f := by
  rw [Multiset.coe_sort]
  apply List.mergeSort_eq_self
  rw [List.pairwise_map]
  apply List.Pairwise.imp _ (List.pairwise_lt_finRange n)
  intro a b hab
  exact hf a b (le_of_lt hab)

end SymSSYTHelpers

namespace SkewPartition

variable {N : ℕ}


/-- Horizontal strip characterization (Proposition prop.sf.strips.entries(a))
    Label: prop.sf.strips.entries

    A skew partition λ/μ is a horizontal strip iff
    λ₁ ≥ μ₁ ≥ λ₂ ≥ μ₂ ≥ ⋯ ≥ λ_N ≥ μ_N. -/
lemma horizontalStrip_iff_entries (s : SkewPartition N) :
    s.isHorizontalStrip ↔
      ∀ i : Fin N, ∀ hi : i.val + 1 < N,
        s.outer.parts i ≥ s.inner.parts i ∧
        s.inner.parts i ≥ s.outer.parts ⟨i.val + 1, hi⟩ := by
  constructor
  · intro h i hi
    exact ⟨s.contained i, h i hi⟩
  · intro h i hi
    exact (h i hi).2

/-- Vertical strip characterization (Proposition prop.sf.strips.entries(b))
    Label: prop.sf.strips.entries

    A skew partition λ/μ is a vertical strip iff
    μᵢ ≤ λᵢ ≤ μᵢ + 1 for each i ∈ [N]. -/
lemma verticalStrip_iff_entries (s : SkewPartition N) :
    s.isVerticalStrip ↔
      ∀ i : Fin N, s.inner.parts i ≤ s.outer.parts i ∧
        s.outer.parts i ≤ s.inner.parts i + 1 := by
  constructor
  · intro h i
    exact ⟨s.contained i, h i⟩
  · intro h i
    exact (h i).2

/-- A horizontal n-strip has size n. -/
lemma isHorizontalNStrip.size_eq {s : SkewPartition N} {n : ℕ} (h : s.isHorizontalNStrip n) :
    s.size = n := h.2

/-- A vertical n-strip has size n. -/
lemma isVerticalNStrip.size_eq {s : SkewPartition N} {n : ℕ} (h : s.isVerticalNStrip n) :
    s.size = n := h.2

/-- A horizontal n-strip is a horizontal strip. -/
lemma isHorizontalNStrip.isHorizontalStrip {s : SkewPartition N} {n : ℕ}
    (h : s.isHorizontalNStrip n) : s.isHorizontalStrip := h.1

/-- A vertical n-strip is a vertical strip. -/
lemma isVerticalNStrip.isVerticalStrip {s : SkewPartition N} {n : ℕ}
    (h : s.isVerticalNStrip n) : s.isVerticalStrip := h.1

/-- The empty skew partition (λ = μ) is a horizontal 0-strip. -/
lemma empty_isHorizontalNStrip (lam : NPartition N) :
    (⟨lam, lam, fun _ => le_refl _⟩ : SkewPartition N).isHorizontalNStrip 0 := by
  constructor
  · intro i hi
    exact lam.weaklyDecreasing ⟨i.val, i.isLt⟩ ⟨i.val + 1, hi⟩ (Nat.le_succ _)
  · simp [size, NPartition.size]

/-- The empty skew partition (λ = μ) is a vertical 0-strip. -/
lemma empty_isVerticalNStrip (lam : NPartition N) :
    (⟨lam, lam, fun _ => le_refl _⟩ : SkewPartition N).isVerticalNStrip 0 := by
  constructor
  · intro i
    exact Nat.le_succ _
  · simp [size, NPartition.size]


section Examples

end Examples

end SkewPartition

/-- Two SSYT are equal if their entries are equal. -/
lemma SSYT.eq_of_entries_eq {lam : NPartition N} {T1 T2 : SSYT lam}
    (h : T1.entries = T2.entries) : T1 = T2 := by
  cases T1; cases T2
  simp only at h
  subst h
  rfl

/-- An SSYT's entries form a valid filling. -/
lemma SSYT.entries_isSSYTFillingNonSkew {lam : NPartition N} (T : SSYT lam) :
    isSSYTFillingNonSkew lam T.entries := ⟨T.rowWeak, T.colStrict⟩

/-- An SSYT's entries are in the valid filling finset. -/
lemma SSYT.entries_mem_ssytFillingFinsetNonSkew {lam : NPartition N} (T : SSYT lam) :
    T.entries ∈ ssytFillingFinsetNonSkew lam := by
  simp only [ssytFillingFinsetNonSkew, Finset.mem_filter, Finset.mem_univ, true_and]
  exact T.entries_isSSYTFillingNonSkew

/-- Every SSYT is in ssytFinset. -/
lemma ssytFinset_mem (lam : NPartition N) (T : SSYT lam) : T ∈ ssytFinset lam := by
  simp only [ssytFinset, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists]
  refine ⟨T.entries, T.entries_mem_ssytFillingFinsetNonSkew, ?_⟩
  simp only [fillingToSSYT]
  cases T
  rfl


/-- A SkewSSYT's entries are in ssytFillingFinset. -/
lemma SkewSSYT.entries_mem_ssytFillingFinset {s : SkewPartition N} (T : SkewSSYT s) :
    T.entries ∈ ssytFillingFinset s := by
  simp only [ssytFillingFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact T.toFilling_isSSYTFilling

/-- Every skew SSYT is a member of skewSSYTFinset.
    This follows from the definition of skewSSYTFinset as the set of ALL skew SSYT. -/
lemma skewSSYTFinset_mem (s : SkewPartition N) (T : SkewSSYT s) :
    T ∈ skewSSYTFinset s := by
  -- T.entries is a filling that satisfies SSYT conditions
  -- We need to show T is in the image of the map
  simp only [skewSSYTFinset, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists]
  -- We need to find T.entries in ssytFillingFinset s that maps to T
  refine ⟨T.entries, T.entries_mem_ssytFillingFinset, ?_⟩
  -- Show that fillingToSkewSSYT T.entries _ = T
  simp only [fillingToSkewSSYT]
  -- Need to show that the resulting SkewSSYT equals T
  cases T
  rfl

/-- Any SSYT of shape 0 equals the unique empty tableau. -/
lemma SSYT.eq_unique (T : SSYT (0 : NPartition N)) : T = SSYT.unique := by
  apply SSYT.eq_of_entries_eq
  funext i j
  exact Fin.elim0 j

/-- The monomial of the unique SSYT of shape 0 is 1. -/
@[simp]
lemma SSYT.toMonomial_unique : (SSYT.unique (N := N)).toMonomial (R := R) = 1 := by
  simp only [SSYT.toMonomial]
  have h : ∀ i : Fin N, ∏ j : Fin ((0 : NPartition N).parts i),
      MvPolynomial.X (SSYT.unique.entries i j) = (1 : MvPolynomial (Fin N) R) := by
    intro i
    haveI : IsEmpty (Fin ((0 : NPartition N).parts i)) := by
      change IsEmpty (Fin 0)
      exact Fin.isEmpty
    exact Fintype.prod_empty _
  simp only [h, Finset.prod_const_one]

/-- The finite set of SSYT of shape 0 is the singleton containing the unique empty tableau. -/
lemma ssytFinset_zero : ssytFinset (0 : NPartition N) = {SSYT.unique} := by
  ext T
  constructor
  · intro _
    simp only [Finset.mem_singleton]
    exact T.eq_unique
  · intro hT
    simp only [Finset.mem_singleton] at hT
    rw [hT]
    exact ssytFinset_mem 0 SSYT.unique

/-- The Schur polynomial of the zero partition is 1.
    This is because the only SSYT of shape 0 is the empty tableau with monomial 1. -/
@[simp]
lemma schur_zero : schur (0 : NPartition N) = (1 : MvPolynomial (Fin N) R) := by
  simp only [schur, ssytFinset_zero, Finset.sum_singleton, SSYT.toMonomial_unique]

/-- ssytToSkewSSYT and skewSSYTToSSYT are inverses (direction 1). -/
lemma ssytToSkewSSYT_skewSSYTToSSYT (lam : Fin N → ℕ) (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (T : SSYT ⟨lam, hlam⟩) :
    skewSSYTToSSYT lam hlam (ssytToSkewSSYT lam hlam T) = T := by
  cases T; rfl

/-- ssytToSkewSSYT and skewSSYTToSSYT are inverses (direction 2). -/
lemma skewSSYTToSSYT_ssytToSkewSSYT (lam : Fin N → ℕ) (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨fun _ => 0, fun _ _ _ => le_refl 0⟩, fun _ => Nat.zero_le _⟩) :
    ssytToSkewSSYT lam hlam (skewSSYTToSSYT lam hlam T) = T := by
  cases T; rfl

/-- ssytToSkewSSYT preserves monomials. -/
lemma ssytToSkewSSYT_toMonomial (lam : Fin N → ℕ) (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (T : SSYT ⟨lam, hlam⟩) :
    (ssytToSkewSSYT lam hlam T).toMonomial = T.toMonomial (R := R) := rfl

/-- When the inner partition is zero, the skew Schur polynomial equals the regular Schur polynomial.
    This is because the skew shape λ/0 is just the shape λ. -/
lemma skewSchur_zero_eq_schur (lam : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
    skewSchur (R := R) ⟨⟨lam, hlam⟩, ⟨fun _ => 0, fun _ _ _ => le_refl 0⟩, fun _ => Nat.zero_le _⟩ =
    schur (R := R) ⟨lam, hlam⟩ := by
  -- Both sides are sums over tableaux. When inner = 0, SkewSSYT is essentially the same as SSYT
  -- since outer.parts i - 0 = outer.parts i for all i.
  unfold skewSchur schur
  -- Use sum_bij with the bijection ssytToSkewSSYT
  symm
  apply Finset.sum_bij (fun T _ => ssytToSkewSSYT lam hlam T)
  · -- ssytToSkewSSYT maps elements to skewSSYTFinset
    intro T _
    exact skewSSYTFinset_mem _ _
  · -- ssytToSkewSSYT is injective
    intro T₁ _ T₂ _ h
    have : skewSSYTToSSYT lam hlam (ssytToSkewSSYT lam hlam T₁) =
           skewSSYTToSSYT lam hlam (ssytToSkewSSYT lam hlam T₂) := by rw [h]
    simp only [ssytToSkewSSYT_skewSSYTToSSYT] at this
    exact this
  · -- ssytToSkewSSYT is surjective
    intro T' _
    refine ⟨skewSSYTToSSYT lam hlam T', ssytFinset_mem _ _, ?_⟩
    exact skewSSYTToSSYT_ssytToSkewSSYT lam hlam T'
  · -- ssytToSkewSSYT preserves monomials
    intro T _
    exact ssytToSkewSSYT_toMonomial lam hlam T


/-- If λ ∈ horizontalNStripPartitions μ n, then μ ⊆ λ. -/
lemma horizontalNStripPartitions_contained (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ horizontalNStripPartitions mu n) :
    mu ≤ lam := by
  simp only [horizontalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter, potentialHorizontalStrips, Fintype.mem_piFinset,
    Finset.mem_Icc] at hf
  intro i
  have hfi : mu.parts i ≤ f i := (hf.1 i).1
  simp only [← heq, toNPartition]
  exact hfi

/-- If λ ∈ horizontalNStripPartitions μ n, then λ/μ is a horizontal strip. -/
lemma horizontalNStripPartitions_isHorizontalStrip (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ horizontalNStripPartitions mu n) :
    (⟨lam, mu, horizontalNStripPartitions_contained mu n lam hlam⟩ : SkewPartition N).isHorizontalStrip := by
  simp only [horizontalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter] at hf
  intro i hi
  simp only [← heq, toNPartition]
  exact hf.2.2.1 i hi

/-- If λ ∈ horizontalNStripPartitions μ n, then |λ| - |μ| = n. -/
lemma horizontalNStripPartitions_size (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ horizontalNStripPartitions mu n) :
    lam.size - mu.size = n := by
  simp only [horizontalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter] at hf
  rw [← heq]
  simp only [toNPartition, NPartition.size, hasSizeDiff] at hf ⊢
  omega

/-- If λ ∈ horizontalNStripPartitions μ n, then the skew partition λ/μ is a horizontal n-strip.
    This combines the horizontal strip condition and size condition into a single predicate. -/
lemma horizontalNStripPartitions_isHorizontalNStrip' (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ horizontalNStripPartitions mu n) :
    (⟨lam, mu, horizontalNStripPartitions_contained mu n lam hlam⟩ : SkewPartition N).isHorizontalNStrip n := by
  have hcontained := horizontalNStripPartitions_contained mu n lam hlam
  simp only [horizontalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter] at hf
  constructor
  · -- horizontal strip condition
    intro i hi
    have heq_parts : lam.parts = f := by rw [← heq]; rfl
    simp only [heq_parts]
    exact hf.2.2.1 i hi
  · -- size condition
    simp only [SkewPartition.size, NPartition.size]
    have heq_parts : lam.parts = f := by rw [← heq]; rfl
    rw [heq_parts]
    simp only [hasSizeDiff] at hf
    have hle : ∑ i, mu.parts i ≤ ∑ i, f i := by
      apply Finset.sum_le_sum
      intro i _
      simp only [potentialHorizontalStrips, Fintype.mem_piFinset, Finset.mem_Icc] at hf
      exact (hf.1 i).1
    have hsize : ∑ i, f i = ∑ i, mu.parts i + n := hf.2.2.2
    omega


/-- If λ ∈ verticalNStripPartitions μ n, then μ ⊆ λ. -/
lemma verticalNStripPartitions_contained (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ verticalNStripPartitions mu n) :
    mu ≤ lam := by
  simp only [verticalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter, potentialVerticalStrips, Fintype.mem_piFinset,
    Finset.mem_Icc] at hf
  intro i
  have hfi : mu.parts i ≤ f i := (hf.1 i).1
  simp only [← heq, toNPartition]
  exact hfi

/-- If λ ∈ verticalNStripPartitions μ n, then λ/μ is a vertical strip. -/
lemma verticalNStripPartitions_isVerticalStrip (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ verticalNStripPartitions mu n) :
    (⟨lam, mu, verticalNStripPartitions_contained mu n lam hlam⟩ : SkewPartition N).isVerticalStrip := by
  simp only [verticalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter] at hf
  intro i
  simp only [← heq, toNPartition]
  exact hf.2.2.1 i

/-- If λ ∈ verticalNStripPartitions μ n, then |λ| - |μ| = n. -/
lemma verticalNStripPartitions_size (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ verticalNStripPartitions mu n) :
    lam.size - mu.size = n := by
  simp only [verticalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter] at hf
  rw [← heq]
  simp only [toNPartition, NPartition.size, hasSizeDiff] at hf ⊢
  omega

/-- If λ ∈ verticalNStripPartitions μ n, then the skew partition λ/μ is a vertical n-strip.
    This combines the vertical strip condition and size condition into a single predicate. -/
lemma verticalNStripPartitions_isVerticalNStrip' (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ verticalNStripPartitions mu n) :
    (⟨lam, mu, verticalNStripPartitions_contained mu n lam hlam⟩ : SkewPartition N).isVerticalNStrip n := by
  have hcontained := verticalNStripPartitions_contained mu n lam hlam
  simp only [verticalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter] at hf
  constructor
  · -- vertical strip condition
    intro i
    have heq_parts : lam.parts = f := by rw [← heq]; rfl
    rw [heq_parts]
    exact hf.2.2.1 i
  · -- size condition
    simp only [SkewPartition.size, NPartition.size]
    have heq_parts : lam.parts = f := by rw [← heq]; rfl
    rw [heq_parts]
    simp only [hasSizeDiff] at hf
    have hle : ∑ i, mu.parts i ≤ ∑ i, f i := by
      apply Finset.sum_le_sum
      intro i _
      simp only [potentialVerticalStrips, Fintype.mem_piFinset, Finset.mem_Icc] at hf
      exact (hf.1 i).1
    have hsize : ∑ i, f i = ∑ i, mu.parts i + n := hf.2.2.2
    omega


/-- Complete characterization of membership in `horizontalNStripPartitions`.

    An N-partition λ is in `horizontalNStripPartitions μ n` if and only if:
    1. μ ⊆ λ (containment): μ_i ≤ λ_i for all i
    2. λ/μ is a horizontal strip: μ_i ≥ λ_{i+1} for all i < N
    3. |λ| - |μ| = n (size constraint)
    4. Each λ_i is bounded by `horizontalStripUpperBound μ n i`

    This characterization is useful for proving that specific partitions
    belong to `horizontalNStripPartitions μ n`. -/
lemma mem_horizontalNStripPartitions_iff (mu : NPartition N) (n : ℕ) (lam : NPartition N) :
    lam ∈ horizontalNStripPartitions mu n ↔
      (∀ i, mu.parts i ≤ lam.parts i) ∧
      isHorizontalStripFun lam.parts mu.parts ∧
      hasSizeDiff mu.parts lam.parts n ∧
      (∀ i, lam.parts i ≤ horizontalStripUpperBound mu n i) := by
  constructor
  · -- Forward direction: membership implies conditions
    intro hlam
    simp only [horizontalNStripPartitions, Finset.mem_image, Finset.mem_attach,
      true_and, Subtype.exists] at hlam
    obtain ⟨f, hf, heq⟩ := hlam
    simp only [Finset.mem_filter, potentialHorizontalStrips, Fintype.mem_piFinset,
      Finset.mem_Icc] at hf
    have hparts : lam.parts = f := by
      simp only [← heq, toNPartition]
    constructor
    · -- containment
      intro i
      rw [hparts]
      exact (hf.1 i).1
    constructor
    · -- horizontal strip
      rw [hparts]
      exact hf.2.2.1
    constructor
    · -- size diff
      rw [hparts]
      exact hf.2.2.2
    · -- upper bound
      intro i
      rw [hparts]
      exact (hf.1 i).2
  · -- Backward direction: conditions imply membership
    intro ⟨hcontained, hstrip, hsize, hbound⟩
    simp only [horizontalNStripPartitions, Finset.mem_image, Finset.mem_attach,
      true_and, Subtype.exists]
    refine ⟨lam.parts, ?_, rfl⟩
    simp only [Finset.mem_filter, potentialHorizontalStrips, Fintype.mem_piFinset,
      Finset.mem_Icc]
    exact ⟨fun i => ⟨hcontained i, hbound i⟩, lam.weaklyDecreasing, hstrip, hsize⟩

/-- Complete characterization of membership in `verticalNStripPartitions`.

    An N-partition λ is in `verticalNStripPartitions μ n` if and only if:
    1. μ ⊆ λ (containment): μ_i ≤ λ_i for all i
    2. λ/μ is a vertical strip: λ_i ≤ μ_i + 1 for all i
    3. |λ| - |μ| = n (size constraint)

    This characterization is useful for proving that specific partitions
    belong to `verticalNStripPartitions μ n`. -/
lemma mem_verticalNStripPartitions_iff (mu : NPartition N) (n : ℕ) (lam : NPartition N) :
    lam ∈ verticalNStripPartitions mu n ↔
      (∀ i, mu.parts i ≤ lam.parts i) ∧
      isVerticalStripFun lam.parts mu.parts ∧
      hasSizeDiff mu.parts lam.parts n := by
  constructor
  · -- Forward direction: membership implies conditions
    intro hlam
    simp only [verticalNStripPartitions, Finset.mem_image, Finset.mem_attach,
      true_and, Subtype.exists] at hlam
    obtain ⟨f, hf, heq⟩ := hlam
    simp only [Finset.mem_filter, potentialVerticalStrips, Fintype.mem_piFinset,
      Finset.mem_Icc] at hf
    have hparts : lam.parts = f := by
      simp only [← heq, toNPartition]
    constructor
    · -- containment
      intro i
      rw [hparts]
      exact (hf.1 i).1
    constructor
    · -- vertical strip
      rw [hparts]
      exact hf.2.2.1
    · -- size diff
      rw [hparts]
      exact hf.2.2.2
  · -- Backward direction: conditions imply membership
    intro ⟨hcontained, hstrip, hsize⟩
    simp only [verticalNStripPartitions, Finset.mem_image, Finset.mem_attach,
      true_and, Subtype.exists]
    refine ⟨lam.parts, ?_, rfl⟩
    simp only [Finset.mem_filter, potentialVerticalStrips, Fintype.mem_piFinset,
      Finset.mem_Icc, verticalStripUpperBound]
    constructor
    · intro i
      exact ⟨hcontained i, hstrip i⟩
    exact ⟨lam.weaklyDecreasing, hstrip, hsize⟩

/-- Helper lemma relating `SkewPartition.size` to `hasSizeDiff` for horizontal strips. -/
lemma hasSizeDiff_of_isHorizontalNStrip (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hcontained : mu ≤ lam)
    (hstrip : (⟨lam, mu, hcontained⟩ : SkewPartition N).isHorizontalNStrip n) :
    hasSizeDiff mu.parts lam.parts n := by
  simp only [hasSizeDiff]
  have hsize := hstrip.2
  simp only [SkewPartition.size, NPartition.size] at hsize
  have hle : (∑ i, mu.parts i) ≤ (∑ i, lam.parts i) := by
    apply Finset.sum_le_sum
    intro i _
    exact hcontained i
  omega

/-- Helper lemma relating `SkewPartition.size` to `hasSizeDiff` for vertical strips. -/
lemma hasSizeDiff_of_isVerticalNStrip (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hcontained : mu ≤ lam)
    (hstrip : (⟨lam, mu, hcontained⟩ : SkewPartition N).isVerticalNStrip n) :
    hasSizeDiff mu.parts lam.parts n := by
  simp only [hasSizeDiff]
  have hsize := hstrip.2
  simp only [SkewPartition.size, NPartition.size] at hsize
  have hle : (∑ i, mu.parts i) ≤ (∑ i, lam.parts i) := by
    apply Finset.sum_le_sum
    intro i _
    exact hcontained i
  omega

/-- Simplified membership criterion for horizontal strip partitions using SkewPartition API.

    This theorem bridges the gap between the `horizontalNStripPartitions` finset
    and the `SkewPartition.isHorizontalNStrip` predicate. -/
lemma mem_horizontalNStripPartitions_of_isHorizontalNStrip (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hcontained : mu ≤ lam)
    (hstrip : (⟨lam, mu, hcontained⟩ : SkewPartition N).isHorizontalNStrip n)
    (hbound : ∀ i, lam.parts i ≤ horizontalStripUpperBound mu n i) :
    lam ∈ horizontalNStripPartitions mu n := by
  rw [mem_horizontalNStripPartitions_iff]
  exact ⟨hcontained, hstrip.1, hasSizeDiff_of_isHorizontalNStrip mu n lam hcontained hstrip, hbound⟩

/-- Simplified membership criterion for vertical strip partitions using SkewPartition API.

    This theorem bridges the gap between the `verticalNStripPartitions` finset
    and the `SkewPartition.isVerticalNStrip` predicate. -/
lemma mem_verticalNStripPartitions_of_isVerticalNStrip (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hcontained : mu ≤ lam)
    (hstrip : (⟨lam, mu, hcontained⟩ : SkewPartition N).isVerticalNStrip n) :
    lam ∈ verticalNStripPartitions mu n := by
  rw [mem_verticalNStripPartitions_iff]
  exact ⟨hcontained, hstrip.1, hasSizeDiff_of_isVerticalNStrip mu n lam hcontained hstrip⟩

/-- The row partition function has n at position 0 and 0 elsewhere. -/
@[simp]
lemma rowPartitionFun_zero (N : ℕ) (n : ℕ) (hN : 0 < N) :
    rowPartitionFun N n hN ⟨0, hN⟩ = n := by
  simp [rowPartitionFun, NPartition.rowPartition]

@[simp]
lemma rowPartitionFun_pos (N : ℕ) (n : ℕ) (hN : 0 < N) (i : Fin N) (hi : 0 < i.val) :
    rowPartitionFun N n hN i = 0 := by
  simp only [rowPartitionFun, NPartition.rowPartition]
  simp only [ite_eq_right_iff]
  omega

/-- The column partition function has 1 at positions < n and 0 elsewhere. -/
@[simp]
lemma colPartitionFun_lt (N : ℕ) (n : ℕ) (hn : n ≤ N) (i : Fin N) (hi : i.val < n) :
    colPartitionFun N n hn i = 1 := by
  simp [colPartitionFun, NPartition.colPartition, hi]

@[simp]
lemma colPartitionFun_ge (N : ℕ) (n : ℕ) (hn : n ≤ N) (i : Fin N) (hi : n ≤ i.val) :
    colPartitionFun N n hn i = 0 := by
  simp [colPartitionFun, NPartition.colPartition, Nat.not_lt.mpr hi]

/-- The row partition function is an N-partition (weakly decreasing). -/
lemma rowPartitionFun_isNPartition (N : ℕ) (n : ℕ) (hN : 0 < N) :
    _root_.IsNPartition (rowPartitionFun N n hN) :=
  (NPartition.rowPartition N n hN).weaklyDecreasing

/-- The column partition function is an N-partition (weakly decreasing). -/
lemma colPartitionFun_isNPartition (N : ℕ) (n : ℕ) (hn : n ≤ N) :
    _root_.IsNPartition (colPartitionFun N n hn) :=
  (NPartition.colPartition N n hn).weaklyDecreasing


/-- The bundled `SkewPartition.isHorizontalStrip` is equivalent to the canonical
    unbundled `isHorizontalStripFun` applied to the outer and inner partitions. -/
lemma SkewPartition.isHorizontalStrip_iff_isHorizontalStripFun (s : SkewPartition N) :
    s.isHorizontalStrip ↔ isHorizontalStripFun s.outer.parts s.inner.parts := Iff.rfl

/-- The bundled `SkewPartition.isVerticalStrip` is equivalent to the canonical
    unbundled `isVerticalStripFun` applied to the outer and inner partitions. -/
lemma SkewPartition.isVerticalStrip_iff_isVerticalStripFun (s : SkewPartition N) :
    s.isVerticalStrip ↔ isVerticalStripFun s.outer.parts s.inner.parts := Iff.rfl

/-- When all entries of a tableau are 0, the content at any position k > 0 is 0.
    This is because no cell has entry k when all entries are 0. -/
lemma contentColGeq_zero_of_allEntriesZero {lam mu : Fin N → ℕ}
    (T : AlgebraicCombinatorics.Tableau lam mu)
    (hZero : allEntriesZero T) (j : ℕ) (k : Fin N) (hk : 0 < k.val) :
    AlgebraicCombinatorics.contentColGeq T j k = 0 := by
  unfold AlgebraicCombinatorics.contentColGeq
  rw [Nat.card_eq_zero]
  left
  constructor
  intro ⟨⟨c, hc_mem, _⟩, hTc⟩
  have h0 : (T ⟨c, hc_mem⟩).val = 0 := hZero ⟨c, hc_mem⟩
  have : k.val = 0 := by rw [← hTc]; exact h0
  omega

/-- **Row partition Yamanouchi characterization (reverse direction):**
    If all entries of T are 0 and T is semistandard, then T is ν-Yamanouchi
    for ν = (n, 0, ..., 0). -/
lemma allEntriesZero_implies_isYamanouchi_rowPartition
    {lam mu : Fin N → ℕ} (hN : 0 < N)
    (T : AlgebraicCombinatorics.Tableau lam mu)
    (hSS : AlgebraicCombinatorics.IsSemistandard T)
    (hZero : allEntriesZero T) :
    ∀ n : ℕ, AlgebraicCombinatorics.IsYamanouchi (rowPartitionFun N n hN) T := by
  intro n
  constructor
  · exact hSS
  · intro j hj i k hik
    simp only [Pi.add_apply]
    -- When all entries are 0, the content at any position k > 0 is 0
    -- So ν + cont = (n + cont_0, 0, ..., 0) which is weakly decreasing
    by_cases hi : i.val = 0
    · by_cases hk : k.val = 0
      · have : i = k := Fin.ext (by omega)
        rw [this]
      · -- k > 0, so rowPartitionFun k = 0 and contentColGeq T j k = 0
        have hk_pos : 0 < k.val := Nat.pos_of_ne_zero hk
        have h1 : rowPartitionFun N n hN k = 0 := rowPartitionFun_pos N n hN k hk_pos
        have h2 : AlgebraicCombinatorics.contentColGeq T j k = 0 :=
          contentColGeq_zero_of_allEntriesZero T hZero j k hk_pos
        simp only [h1, h2]
        omega
    · -- i > 0, so k ≥ i > 0, thus both rowPartitionFun and contentColGeq are 0
      have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi
      have hk_pos : 0 < k.val := by have : i.val ≤ k.val := hik; omega
      have h1i : rowPartitionFun N n hN i = 0 := rowPartitionFun_pos N n hN i hi_pos
      have h1k : rowPartitionFun N n hN k = 0 := rowPartitionFun_pos N n hN k hk_pos
      have h2i : AlgebraicCombinatorics.contentColGeq T j i = 0 :=
        contentColGeq_zero_of_allEntriesZero T hZero j i hi_pos
      have h2k : AlgebraicCombinatorics.contentColGeq T j k = 0 :=
        contentColGeq_zero_of_allEntriesZero T hZero j k hk_pos
      simp only [h1i, h1k, h2i, h2k]
      omega

/-- symToRowSSYT and rowSSYTToSym are inverses (Sym → SSYT → Sym). -/
lemma rowSSYTToSym_symToRowSSYT (hN : 0 < N) (n : ℕ) (s : Sym (Fin N) n) :
    rowSSYTToSym hN n (symToRowSSYT hN n s) = s := by
  unfold rowSSYTToSym
  simp only [symToRowSSYT, symToWeaklyIncreasing]
  exact weaklyIncreasingToSym_symToWeaklyIncreasing n s

/-- symToRowSSYT preserves monomials. -/
lemma symToRowSSYT_toMonomial (hN : 0 < N) (n : ℕ) (s : Sym (Fin N) n) :
    (symToRowSSYT hN n s).toMonomial (R := R) = (s.1.map MvPolynomial.X).prod := by
  -- The product over the single-row tableau equals the Sym monomial
  -- This follows from sym_monomial_eq_weaklyIncreasing_prod
  unfold SSYT.toMonomial symToRowSSYT
  simp only
  -- The product over i : Fin N simplifies because only i = 0 contributes
  rw [Finset.prod_eq_single ⟨0, hN⟩]
  · -- Main case: i = 0
    rw [sym_monomial_eq_weaklyIncreasing_prod]
    apply Finset.prod_congr rfl
    intro j _
    congr 1
  · -- Other rows contribute 1 (empty product)
    intro i _ hi
    have hi_pos : 0 < i.val := by
      by_contra h
      push Not at h
      have : i.val = 0 := Nat.eq_zero_of_le_zero h
      apply hi
      ext
      exact this
    have hparts : (NPartition.rowPartition N n hN).parts i = 0 :=
      NPartition.rowPartition_parts_pos N n hN i hi_pos
    -- Since parts i = 0, Fin (parts i) is empty, so the product is 1
    haveI hemp : IsEmpty (Fin ((NPartition.rowPartition N n hN).parts i)) := by
      simp only [hparts]
      exact Fin.isEmpty
    exact Fintype.prod_empty _
  · -- ⟨0, hN⟩ ∈ univ is always true
    intro h
    exact (h (Finset.mem_univ _)).elim

/-- The complete homogeneous symmetric polynomial h_n equals the Schur polynomial
    indexed by the row partition (n, 0, ..., 0).

    This is because:
    - The only SSYT of shape (n, 0, ..., 0) is a single row of n boxes
    - A single row SSYT with entries from Fin N is exactly a weakly increasing sequence
    - Such sequences correspond to multisets of size n from Fin N
    - The monomial of such a tableau is exactly (s.1.map X).prod for s : Sym (Fin N) n

    This lemma enables deriving the horizontal Pieri rule from Littlewood-Richardson. -/
lemma hsymm_eq_schur_rowPartition (hN : 0 < N) (n : ℕ) :
    hsymm (Fin N) R n = schur (NPartition.rowPartition N n hN) := by
  -- Both sides are sums of monomials
  -- hsymm sums over Sym (Fin N) n
  -- schur sums over SSYT of row partition shape
  -- We use symToRowSSYT as a bijection
  unfold hsymm schur
  apply Finset.sum_bij (fun s _ => symToRowSSYT hN n s)
  · -- symToRowSSYT maps to ssytFinset
    intro s _
    exact ssytFinset_mem _ _
  · -- symToRowSSYT is injective
    intro s₁ _ s₂ _ h
    have h' : rowSSYTToSym hN n (symToRowSSYT hN n s₁) =
              rowSSYTToSym hN n (symToRowSSYT hN n s₂) := by rw [h]
    simp only [rowSSYTToSym_symToRowSSYT] at h'
    exact h'
  · -- symToRowSSYT is surjective onto ssytFinset
    intro T _
    refine ⟨rowSSYTToSym hN n T, Finset.mem_univ _, ?_⟩
    -- Need to show symToRowSSYT (rowSSYTToSym T) = T
    -- This requires showing that for a weakly increasing sequence,
    -- sorting gives back the same sequence
    apply SSYT.eq_of_entries_eq
    funext i j
    unfold symToRowSSYT rowSSYTToSym weaklyIncreasingToSym
    simp only
    split_ifs with hi
    · -- Row 0 case: need to show sorted entries = original entries
      have hrow0 : (NPartition.rowPartition N n hN).parts ⟨0, hN⟩ = n := by
        simp [NPartition.rowPartition]
      -- Define the entries function from row 0
      let entries0 : Fin n → Fin N := fun k =>
        T.entries ⟨0, hN⟩ ⟨k.val, by rw [hrow0]; exact k.isLt⟩
      -- entries0 is weakly increasing by SSYT row condition
      have h_weak : ∀ a b : Fin n, a ≤ b → entries0 a ≤ entries0 b := by
        intro a b hab
        exact T.rowWeak ⟨0, hN⟩ _ _ hab
      -- Use the helper lemma: sorting a weakly increasing list gives the same list
      have hsort := sort_weaklyIncreasing_list_eq entries0 h_weak
      -- Goal: sorted[j.val] = T.entries i j where i.val = 0
      have hi_eq : i = ⟨0, hN⟩ := Fin.ext hi
      subst hi_eq
      -- After subst, need: sorted[j.val] = T.entries ⟨0, hN⟩ j
      have hlen : ((Multiset.ofList ((List.finRange n).map entries0)).sort (· ≤ ·)).length = n := by
        rw [hsort]; simp
      simp only [symToWeaklyIncreasing, List.get_eq_getElem]
      -- Goal: sorted[j.val] = T.entries ⟨0, hN⟩ j
      -- where sorted = (ofList (finRange.map entries0)).sort
      -- Use List.getElem_of_eq to rewrite sorted to the original list
      have hj_bound : j.val < ((Multiset.ofList ((List.finRange n).map entries0)).sort (· ≤ ·)).length := by
        simp only [hlen]; exact j.isLt
      rw [List.getElem_of_eq hsort hj_bound]
      -- Now goal is: (finRange.map entries0)[j.val] = T.entries ⟨0, hN⟩ j
      simp only [List.getElem_map, List.getElem_finRange]
      -- entries0 ⟨j.val, _⟩ = T.entries ⟨0, hN⟩ ⟨j.val, _⟩ by definition
      -- And T.entries ⟨0, hN⟩ ⟨j.val, _⟩ = T.entries ⟨0, hN⟩ j by Fin.ext
      rfl
    · -- Non-row-0 case: vacuously true since j is from Fin 0
      have hj := j.isLt
      simp only [NPartition.rowPartition, hi, ↓reduceIte] at hj
      exact (Nat.not_lt_zero j.val hj).elim
  · -- Monomial preservation
    intro s _
    exact (symToRowSSYT_toMonomial hN n s).symm

/-- Column entries are strictly increasing - consecutive case -/
lemma colSSYTEntry_succ_lt (n : ℕ) (hn : n ≤ N)
    (T : SSYT (NPartition.colPartition N n hn))
    (k : ℕ) (hk : k < n) (hk1 : k + 1 < n) :
    colSSYTEntry n hn T k hk < colSSYTEntry n hn T (k + 1) hk1 := by
  unfold colSSYTEntry
  have hkN : k < N := Nat.lt_of_lt_of_le hk hn
  have hk1N : k + 1 < N := Nat.lt_of_lt_of_le hk1 hn
  have hj : (0 : ℕ) < (NPartition.colPartition N n hn).parts ⟨k + 1, hk1N⟩ := by
    simp [NPartition.colPartition, hk1]
  exact T.colStrict ⟨k, hkN⟩ hk1N ⟨0, by simp [NPartition.colPartition, hk]⟩ hj

/-- Column entries are strictly increasing - general case -/
lemma colSSYTEntry_strictMono (n : ℕ) (hn : n ≤ N)
    (T : SSYT (NPartition.colPartition N n hn))
    (k₁ k₂ : ℕ) (hk₁ : k₁ < n) (hk₂ : k₂ < n) (hlt : k₁ < k₂) :
    colSSYTEntry n hn T k₁ hk₁ < colSSYTEntry n hn T k₂ hk₂ := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hlt
  clear hlt
  induction d generalizing k₁ with
  | zero =>
    simp only [Nat.add_zero] at hd
    subst hd
    exact colSSYTEntry_succ_lt n hn T k₁ hk₁ hk₂
  | succ d ih =>
    have hk1p1_lt_n : k₁ + 1 < n := by omega
    have h1 := colSSYTEntry_succ_lt n hn T k₁ hk₁ hk1p1_lt_n
    have h2 := ih (k₁ + 1) hk1p1_lt_n (by omega)
    exact lt_trans h1 h2

/-- The image has cardinality n because entries are strictly increasing -/
lemma colSSYTToFinset_card (n : ℕ) (hn : n ≤ N)
    (T : SSYT (NPartition.colPartition N n hn)) :
    (colSSYTToFinset n hn T).card = n := by
  unfold colSSYTToFinset
  rw [Finset.card_image_of_injective]
  · simp
  · intro k₁ k₂ heq
    simp only at heq
    by_contra hne
    rcases Nat.lt_trichotomy k₁.val k₂.val with hlt | heq' | hgt
    · have hstrict := colSSYTEntry_strictMono n hn T k₁.val k₂.val k₁.isLt k₂.isLt hlt
      rw [heq] at hstrict
      exact lt_irrefl _ hstrict
    · exact hne (Fin.ext heq')
    · have hstrict := colSSYTEntry_strictMono n hn T k₂.val k₁.val k₂.isLt k₁.isLt hgt
      rw [heq] at hstrict
      exact lt_irrefl _ hstrict

/-- Sorting colSSYTToFinset gives back the original entries as a list -/
lemma colSSYTToFinset_sort_eq (n : ℕ) (hn : n ≤ N)
    (T : SSYT (NPartition.colPartition N n hn)) :
    (colSSYTToFinset n hn T).sort (· ≤ ·) =
    List.ofFn (fun k : Fin n => colSSYTEntry n hn T k.val k.isLt) := by
  -- colSSYTToFinset = univ.image f = (List.ofFn f).toFinset
  unfold colSSYTToFinset
  rw [Fin.univ_image_def]
  -- Now use List.toFinset_sort
  have hinj : Function.Injective (fun k : Fin n => colSSYTEntry n hn T k.val k.isLt) := by
    intro k₁ k₂ heq
    by_contra hne
    rcases Nat.lt_trichotomy k₁.val k₂.val with hlt | heq' | hgt
    · have hstrict := colSSYTEntry_strictMono n hn T k₁.val k₂.val k₁.isLt k₂.isLt hlt
      simp only at heq
      rw [heq] at hstrict
      exact lt_irrefl _ hstrict
    · exact hne (Fin.ext heq')
    · have hstrict := colSSYTEntry_strictMono n hn T k₂.val k₁.val k₂.isLt k₁.isLt hgt
      simp only at heq
      rw [heq] at hstrict
      exact lt_irrefl _ hstrict
  rw [List.toFinset_sort (· ≤ ·) (List.nodup_ofFn.mpr hinj)]
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact le_of_lt (colSSYTEntry_strictMono n hn T i.val j.val i.isLt j.isLt hij)

/-- Helper: product over `Fin (if P then 1 else 0)` simplifies based on P -/
lemma prod_fin_ite {α : Type*} [CommMonoid α] (P : Prop) [Decidable P]
    (f : Fin (if P then 1 else 0) → α) :
    ∏ j : Fin (if P then 1 else 0), f j =
    if h : P then f ⟨0, by simp [h]⟩ else 1 := by
  split_ifs with h
  · have heq : (if P then 1 else 0) = 1 := if_pos h
    rw [Fintype.prod_eq_single (⟨0, by simp [heq]⟩ : Fin (if P then 1 else 0))]
    intro b hb
    have hb0 : b.val = 0 := by
      have hlt : b.val < (if P then 1 else 0) := b.isLt
      simp only [h, ite_true] at hlt
      omega
    exact (hb (Fin.ext hb0)).elim
  · have heq : (if P then 1 else 0) = 0 := if_neg h
    have hEmpty : IsEmpty (Fin (if P then 1 else 0)) := by rw [heq]; exact Fin.isEmpty
    haveI : IsEmpty (Fin (if P then 1 else 0)) := hEmpty
    exact Fintype.prod_empty f

/-- Helper: product over list map equals product over finset -/
lemma list_map_prod_eq_finset_prod {α : Type*} [DecidableEq α] {M : Type*} [CommMonoid M]
    (l : List α) (f : α → M) (hl : l.Nodup) :
    (l.map f).prod = ∏ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have hnodup' : l.Nodup := hl.2
    have hna : a ∉ l := hl.1
    simp only [List.map_cons, List.prod_cons, List.toFinset_cons]
    rw [Finset.prod_insert (by simp [hna])]
    congr 1
    exact ih hnodup'

/-- finsetToColSSYT preserves monomials -/
lemma finsetToColSSYT_toMonomial (n : ℕ) (hn : n ≤ N) (s : Finset (Fin N)) (hs : s.card = n) :
    (finsetToColSSYT n hn s hs).toMonomial (R := R) = ∏ i ∈ s, MvPolynomial.X i := by
  -- The proof establishes that the monomial of the column SSYT equals the product over s.
  -- The SSYT has entries in rows 0..n-1 (each with 1 box), and no boxes elsewhere.
  -- For rows i < n: one box with entry = (s.sort).get i
  -- For rows i ≥ n: no boxes (empty product = 1)
  -- So the monomial is ∏_{i < n} X((s.sort).get i) = ∏_{x ∈ s} X(x)
  unfold SSYT.toMonomial
  -- Step 1: Simplify inner product using prod_fin_ite
  have h1 : ∀ i : Fin N, ∏ j : Fin ((NPartition.colPartition N n hn).parts i),
      MvPolynomial.X ((finsetToColSSYT n hn s hs).entries i j) =
      if hi : i.val < n then
        MvPolynomial.X ((s.sort (· ≤ ·)).get ⟨i.val, by rw [Finset.length_sort, hs]; exact hi⟩)
      else (1 : MvPolynomial (Fin N) R) := by
    intro i
    have hparts : (NPartition.colPartition N n hn).parts i = if i.val < n then 1 else 0 := by
      by_cases hi : i.val < n
      · rw [NPartition.colPartition_parts_lt N n hn i hi, if_pos hi]
      · rw [NPartition.colPartition_parts_ge N n hn i (Nat.le_of_not_lt hi), if_neg hi]
    refine (Fintype.prod_equiv (finCongr hparts)
      (fun j => MvPolynomial.X ((finsetToColSSYT n hn s hs).entries i j))
      (fun j => MvPolynomial.X ((finsetToColSSYT n hn s hs).entries i (Fin.cast hparts.symm j)))
      (fun j => by simp [finCongr_apply, Fin.cast_cast])).trans ?_
    rw [prod_fin_ite (i.val < n)]
    split_ifs with hi <;> simp only [finsetToColSSYT, hi, dite_true, Fin.cast_eq_self]
  conv_lhs => arg 2; ext i; rw [h1 i]
  -- Step 2: Product over Fin N with condition equals product over Fin n
  rw [← Finset.prod_filter_mul_prod_filter_not (s := Finset.univ) (p := fun i : Fin N => i.val < n)]
  have h2 : ∏ i ∈ Finset.univ.filter (fun i : Fin N => ¬i.val < n),
      (if hi : i.val < n then
        MvPolynomial.X ((s.sort (· ≤ ·)).get ⟨i.val, by rw [Finset.length_sort, hs]; exact hi⟩)
      else (1 : MvPolynomial (Fin N) R)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hi, dite_false]
  rw [h2, mul_one]
  -- Step 3: Reindex from filter to image
  have h_bij : (Finset.univ.filter (fun i : Fin N => i.val < n)) =
      Finset.univ.image (fun k : Fin n => ⟨k.val, lt_of_lt_of_le k.isLt hn⟩) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · intro ⟨k, hk⟩
      rw [Fin.ext_iff] at hk
      rw [← hk]
      exact k.isLt
  rw [h_bij, Finset.prod_image]
  · -- Step 4: Simplify dite with known condition
    have h3 : ∀ k : Fin n, (if hi : (⟨k.val, lt_of_lt_of_le k.isLt hn⟩ : Fin N).val < n then
        MvPolynomial.X ((s.sort (· ≤ ·)).get ⟨(⟨k.val, lt_of_lt_of_le k.isLt hn⟩ : Fin N).val,
          by rw [Finset.length_sort, hs]; exact hi⟩)
      else (1 : MvPolynomial (Fin N) R)) =
      MvPolynomial.X ((s.sort (· ≤ ·)).get ⟨k.val, by rw [Finset.length_sort, hs]; exact k.isLt⟩) := by
      intro k
      simp only [k.isLt, dite_true]
    simp_rw [h3]
    -- Step 5: Product over Fin n equals product over s via sorted list
    have hlen : (s.sort (· ≤ ·)).length = n := by rw [Finset.length_sort, hs]
    rw [← List.prod_ofFn]
    have h4 : List.ofFn (fun k : Fin n =>
        (MvPolynomial.X ((s.sort (· ≤ ·)).get ⟨k.val, by rw [hlen]; exact k.isLt⟩) :
          MvPolynomial (Fin N) R)) =
        (s.sort (· ≤ ·)).map MvPolynomial.X := by
      apply List.ext_get
      · simp only [List.length_ofFn, List.length_map, hlen]
      · intro i _ _; simp only [List.get_eq_getElem, List.getElem_ofFn, List.getElem_map]
    rw [h4, list_map_prod_eq_finset_prod _ _ (s.sort_nodup (· ≤ ·)), s.sort_toFinset (· ≤ ·)]
  · -- Injectivity of the embedding Fin n → Fin N
    intro k₁ _ k₂ _ heq
    simp only [Fin.mk.injEq] at heq
    exact Fin.ext heq


/-- The elementary symmetric polynomial e_n equals the Schur polynomial
    indexed by the column partition (1, 1, ..., 1, 0, ..., 0) with n ones.

    This is because:
    - The only SSYT of shape (1, 1, ..., 1, 0, ..., 0) is a single column of n boxes
    - A single column SSYT with entries from Fin N must have strictly increasing entries
    - Such sequences correspond to subsets of size n from Fin N
    - The monomial of such a tableau is exactly ∏_{i ∈ s} X_i for s : Finset (Fin N)

    This lemma enables deriving the vertical Pieri rule from Littlewood-Richardson.

    **Proof structure**:
    1. Both sides are sums of monomials
    2. esymm sums over powersetCard n univ with monomial ∏_{i ∈ s} X_i
    3. schur sums over SSYT of shape (1,...,1,0,...,0) with monomial T.toMonomial
    4. For column partition, SSYT entries in column 0 form strictly increasing sequences
    5. The bijection: s ↦ SSYT with entries = sorted(s) in column 0
    6. Weight preservation: ∏_{i ∈ s} X_i = T.toMonomial -/
lemma esymm_eq_schur_colPartition (n : ℕ) (hn : n ≤ N) :
    esymm (Fin N) R n = schur (NPartition.colPartition N n hn) := by
  -- The proof establishes a bijection between:
  -- - Finset (Fin N) of size n (subsets of size n)
  -- - SSYT of shape (1, 1, ..., 1, 0, ..., 0) (single-column tableaux)
  -- Both have the same monomials.
  unfold esymm schur
  apply Finset.sum_bij (fun s hs => finsetToColSSYT n hn s (Finset.mem_powersetCard.mp hs).2)
  · -- finsetToColSSYT maps to ssytFinset
    intro s _
    exact ssytFinset_mem _ _
  · -- finsetToColSSYT is injective
    intro s₁ hs₁ s₂ hs₂ heq
    have h1 : s₁.card = n := (Finset.mem_powersetCard.mp hs₁).2
    have h2 : s₂.card = n := (Finset.mem_powersetCard.mp hs₂).2
    -- The entries of the SSYT determine the sorted list, which determines the set
    ext x
    have hlen1 : (s₁.sort (· ≤ ·)).length = n := by rw [Finset.length_sort, h1]
    have hlen2 : (s₂.sort (· ≤ ·)).length = n := by rw [Finset.length_sort, h2]
    constructor
    · intro hx
      -- x ∈ s₁ means x appears in s₁.sort at some index
      have hmem1 : x ∈ s₁.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hx
      rw [List.mem_iff_get] at hmem1
      obtain ⟨idx, hget1⟩ := hmem1
      have hidx_lt : idx.val < n := by rw [← hlen1]; exact idx.isLt
      -- The entry at position idx in finsetToColSSYT s₁ is x
      have hentry1 : (finsetToColSSYT n hn s₁ h1).entries ⟨idx.val, Nat.lt_of_lt_of_le hidx_lt hn⟩
          ⟨0, by simp [NPartition.colPartition, hidx_lt]⟩ = x := by
        simp only [finsetToColSSYT]
        simp only [hidx_lt, ↓reduceDIte, hget1]
      -- Since finsetToColSSYT s₁ = finsetToColSSYT s₂, the same entry in s₂ is x
      rw [heq] at hentry1
      simp only [finsetToColSSYT, hidx_lt, ↓reduceDIte] at hentry1
      have hmem2 : (s₂.sort (· ≤ ·)).get ⟨idx.val, by rw [hlen2]; exact hidx_lt⟩ ∈ s₂.sort (· ≤ ·) :=
        List.get_mem _ _
      rw [← hentry1]
      exact (Finset.mem_sort (· ≤ ·)).mp hmem2
    · intro hx
      -- Symmetric argument
      have hmem2 : x ∈ s₂.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hx
      rw [List.mem_iff_get] at hmem2
      obtain ⟨idx, hget2⟩ := hmem2
      have hidx_lt : idx.val < n := by rw [← hlen2]; exact idx.isLt
      have hentry2 : (finsetToColSSYT n hn s₂ h2).entries ⟨idx.val, Nat.lt_of_lt_of_le hidx_lt hn⟩
          ⟨0, by simp [NPartition.colPartition, hidx_lt]⟩ = x := by
        simp only [finsetToColSSYT]
        simp only [hidx_lt, ↓reduceDIte, hget2]
      rw [← heq] at hentry2
      simp only [finsetToColSSYT, hidx_lt, ↓reduceDIte] at hentry2
      have hmem1 : (s₁.sort (· ≤ ·)).get ⟨idx.val, by rw [hlen1]; exact hidx_lt⟩ ∈ s₁.sort (· ≤ ·) :=
        List.get_mem _ _
      rw [← hentry2]
      exact (Finset.mem_sort (· ≤ ·)).mp hmem1
  · -- finsetToColSSYT is surjective onto ssytFinset
    intro T _
    -- The proof shows that for any SSYT T of column partition shape,
    -- colSSYTToFinset T is a preimage under finsetToColSSYT.
    -- This follows because:
    -- 1. colSSYTToFinset extracts the entries of T (which form a strictly increasing sequence)
    -- 2. Sorting colSSYTToFinset gives back the original entries
    -- 3. finsetToColSSYT on this sorted set reconstructs T
    have hcard := colSSYTToFinset_card n hn T
    refine ⟨colSSYTToFinset n hn T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩
    -- Show the two SSYTs have equal entries
    have hsort := colSSYTToFinset_sort_eq n hn T
    -- Two SSYTs are equal iff their entries are equal
    cases' T with T_entries T_rowWeak T_colStrict
    simp only [finsetToColSSYT]
    congr 1
    funext i
    funext j
    by_cases hi : i.val < n
    · -- Case i.val < n: both have an entry in column 0
      simp only [hi, dite_true]
      -- The sorted list of colSSYTToFinset is List.ofFn (colSSYTEntry ...)
      -- j must be ⟨0, _⟩ since parts i = 1 for i.val < n
      have hj0 : j.val = 0 := by
        have hj_lt := j.isLt
        simp only [NPartition.colPartition, hi, ite_true] at hj_lt
        omega
      -- Get the entry at position i.val from the sorted list
      -- LHS: sorted_list.get ⟨i.val, _⟩
      -- RHS: T_entries i j
      -- Using hsort: sorted_list = List.ofFn (colSSYTEntry ...)
      -- So LHS = colSSYTEntry n hn T i.val hi = T_entries ⟨i.val, _⟩ ⟨0, _⟩
      simp only [hsort, List.get_eq_getElem, List.getElem_ofFn]
      -- Now show colSSYTEntry equals T_entries
      unfold colSSYTEntry
      simp only []  -- normalizes goal for congr
      -- Need to show T_entries ⟨i.val, _⟩ ⟨0, _⟩ = T_entries i j
      -- This follows because j.val = 0
      congr 1
      exact Fin.ext hj0.symm
    · -- Case i.val ≥ n: both have no entries (Fin 0 for column index)
      simp only [hi, dite_false]
      -- j : Fin (parts i) where parts i = 0 for i.val ≥ n
      have hj_absurd := j.isLt
      simp only [NPartition.colPartition, hi, ite_false] at hj_absurd
      exact (Nat.not_lt_zero j.val hj_absurd).elim
  · -- Monomial preservation
    intro s hs
    exact (finsetToColSSYT_toMonomial n hn s (Finset.mem_powersetCard.mp hs).2).symm


/-- First Pieri rule (Theorem thm.sf.pieri(a))
    Label: exe.sf.pieri

    h_n · s_μ = ∑_{λ/μ is horizontal n-strip} s_λ

    where h_n is the n-th complete homogeneous symmetric polynomial.

    This is Exercise exe.sf.pieri in the TeX source. The proof requires the
    Robinson-Schensted-Knuth (RSK) row insertion bijection, which is not yet
    formalized in this project. -/
lemma pieri_horizontal (n : ℕ) (mu : NPartition N) :
    hsymm (Fin N) R n * schur mu =
      ∑ lam ∈ horizontalNStripPartitions mu n, schur lam := by
  sorry -- [exercise] Exercise exe.sf.pieri from TeX source (requires RSK row insertion)

/-- Second Pieri rule (Theorem thm.sf.pieri(b))
    Label: exe.sf.pieri

    e_n · s_μ = ∑_{λ/μ is vertical n-strip} s_λ

    where e_n is the n-th elementary symmetric polynomial.

    This is Exercise exe.sf.pieri in the TeX source. The proof requires the
    Robinson-Schensted-Knuth (RSK) column insertion bijection, or alternatively
    can be derived from `pieri_horizontal` via the ω-involution. -/
lemma pieri_vertical (n : ℕ) (mu : NPartition N) :
    esymm (Fin N) R n * schur mu =
      ∑ lam ∈ verticalNStripPartitions mu n, schur lam := by
  sorry -- [exercise] Exercise exe.sf.pieri from TeX source (requires RSK column insertion)

/-- hsymmExt is symmetric. -/
lemma hsymmExt_isSymmetric (n : ℤ) : (hsymmExt (N := N) (R := R) n).IsSymmetric := by
  unfold hsymmExt
  split_ifs with h
  · exact hsymm_isSymmetric (Fin N) R n.toNat
  · exact IsSymmetric.zero

/-- Second Jacobi-Trudi formula (Exercise exe.sf.jt-e)
    Label: thm.sf.jt-e
    Status: EXERCISE (exe.sf.jt-e in tex source)

    s_{λ/μ} = det((e_{λᵢᵗ - μⱼᵗ - i + j})_{1 ≤ i,j ≤ N})

    where λᵗ and μᵗ are the transposes of λ and μ, and e_n denotes the n-th
    elementary symmetric polynomial (with e_n = 0 for n < 0).

    This is a 6-point exercise with no hint provided in the TeX source.

    ## References

    - [Stanley, EC2, Theorem 7.16.1]
    - [Grinberg-Reiner, Section 2.4]
    - [Fulton, Young Tableaux, Section 4.3] -/
lemma jacobiTrudi_e (lam mu : Fin N → ℕ)
    (lamt muT : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hlamt : ∀ i j : Fin N, i ≤ j → lamt j ≤ lamt i)
    (hmuT : ∀ i j : Fin N, i ≤ j → muT j ≤ muT i)
    (hcontained : ∀ i, mu i ≤ lam i)
    (htranspose_lam : NPartition.IsTranspose lam lamt)
    (htranspose_mu : NPartition.IsTranspose mu muT)
    :
    skewSchur (R := R) ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ =
      (Matrix.of fun i j =>
        let n := (lamt i : ℤ) - (muT j : ℤ) - (i.val : ℤ) + (j.val : ℤ)
        if 0 ≤ n then esymm (Fin N) R n.toNat else 0).det := by
  sorry -- [exercise]

/-- The source x-coordinates are weakly decreasing.
    This follows from the partition being weakly decreasing:
    μᵢ - i ≥ μⱼ - j when i ≤ j, since μᵢ ≥ μⱼ and i ≤ j. -/
lemma jacobiTrudiSourceX_antitone (mu : Fin N → ℕ)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i) :
    ∀ i j : Fin N, i ≤ j → jacobiTrudiSourceX mu j ≤ jacobiTrudiSourceX mu i := by
  intro i j hij
  unfold jacobiTrudiSourceX
  have h1 : (mu j : ℤ) ≤ (mu i : ℤ) := Int.ofNat_le.mpr (hmu i j hij)
  have h2 : (i.val : ℤ) ≤ (j.val : ℤ) := Int.ofNat_le.mpr (Fin.val_fin_le.mpr hij)
  omega

/-- The target x-coordinates are weakly decreasing.
    This follows from the partition being weakly decreasing. -/
lemma jacobiTrudiTargetX_antitone (lam : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
    ∀ i j : Fin N, i ≤ j → jacobiTrudiTargetX lam j ≤ jacobiTrudiTargetX lam i := by
  intro i j hij
  unfold jacobiTrudiTargetX
  have h1 : (lam j : ℤ) ≤ (lam i : ℤ) := Int.ofNat_le.mpr (hlam i j hij)
  have h2 : (i.val : ℤ) ≤ (j.val : ℤ) := Int.ofNat_le.mpr (Fin.val_fin_le.mpr hij)
  omega

/-- The path from A_i to B_j has length λ_j - μ_i - j + i (when non-negative).
    This equals the index of h in the Jacobi-Trudi matrix entry (j, i). -/
lemma jacobiTrudiPathLength (lam mu : Fin N → ℕ) (i j : Fin N) :
    jacobiTrudiTargetX lam j - jacobiTrudiSourceX mu i =
      (lam j : ℤ) - (mu i : ℤ) - (j.val : ℤ) + (i.val : ℤ) := by
  unfold jacobiTrudiTargetX jacobiTrudiSourceX
  ring

/-- The Jacobi-Trudi matrix entry (i, j) equals h_{path length from A_j to B_i}.
    Note: The path is from source A_j to target B_i. This matches the LGV convention
    where M_{i,j} = ∑_{p : A_i → B_j} w(p), but with the matrix transposed.
    Equivalently, the Jacobi-Trudi matrix is the transpose of the LGV path weight matrix. -/
lemma jacobiTrudiMatrixH_eq_pathLength (lam mu : Fin N → ℕ) (i j : Fin N) :
    jacobiTrudiMatrixH (R := R) lam mu i j =
      hsymmExt (N := N) (R := R) (jacobiTrudiTargetX lam i - jacobiTrudiSourceX mu j) := by
  unfold jacobiTrudiMatrixH jacobiTrudiTargetX jacobiTrudiSourceX
  simp only [Matrix.of_apply]
  congr 1
  ring

/-- The weight of a path obtained from sorting a Sym equals the Sym product. -/
lemma symToLatticePath_weight {a c : ℤ} (s : Sym (Fin N) (c - a).toNat) :
    (symToLatticePath s).weight (R := R) = (s.1.map (fun j => X j)).prod := by
  simp only [symToLatticePath, LatticePath.weight]
  have hsort : ↑(s.1.sort (· ≤ ·)) = s.1 := Multiset.sort_eq s.1 (· ≤ ·)
  conv_rhs => rw [← hsort, Multiset.map_coe, Multiset.prod_coe]

/-- Observation 1 from the proof of Theorem thm.sf.jt-h:
    The sum of path weights from (a, 1) to (c, N) in ℤ² equals h_{c-a}.

    This follows from Proposition prop.lgv.1-paths.ct.
    The key insight is that the weakly increasing sequences of length n
    with entries in [N] are in bijection with multisets of size n from [N],
    which are exactly what h_n counts. -/
lemma pathWeightSum_eq_hsymm (a c : ℤ) :
    ∑ p ∈ latticePathFinset (N := N) a c, p.weight (R := R) = hsymmExt (N := N) (R := R) (c - a) := by
  unfold hsymmExt latticePathFinset
  split_ifs with h
  · -- Case c - a ≥ 0: use the bijection between paths and Sym
    have heq : ∑ p : LatticePath (N := N) a c, p.weight (R := R) =
               ∑ s : Sym (Fin N) (c - a).toNat, (symToLatticePath s).weight (R := R) := by
      apply Finset.sum_equiv latticePathSymEquiv
      · intro p; simp
      · intro p _; simp [latticePathSymEquiv, symToLatticePath_toSym]
    rw [heq]
    rw [Finset.sum_congr rfl (fun s _ => symToLatticePath_weight s)]
    -- hsymm is defined as ∑ s : Sym (Fin N) n, (s.1.map X).prod
    rfl
  · -- Case c - a < 0: both sides are 0
    simp

/-- Converting a list product to a finset product over indices. -/
lemma list_prod_map_X_eq_finset_prod (l : List (Fin N)) (n : ℕ) (h : l.length = n) :
    (l.map (fun j => MvPolynomial.X (R := R) j)).prod =
    ∏ k : Fin n, MvPolynomial.X (l.get ⟨k.val, by rw [h]; exact k.isLt⟩) := by
  subst h
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.get_cons_succ, List.get]
    rw [mul_comm, ih, mul_comm]

/-- The weight of a nipat equals the monomial of the corresponding tableau. -/
lemma nipatToSSYT_weight {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) :
    np.weight (R := R) = (nipatToSSYT np).toMonomial := by
  unfold Nipat.weight SkewSSYT.toMonomial
  congr 1
  funext i
  unfold LatticePath.weight
  have hlen := nipat_path_length np i
  rw [list_prod_map_X_eq_finset_prod _ _ hlen]
  congr 1

/-- Observation 2 from the proof of Theorem thm.sf.jt-h:
    There is a bijection between nipats from 𝐀 to 𝐁 and SSYT(λ/μ).

    The bijection sends a nipat 𝐩 = (p₁, ..., pₖ) to the tableau T(𝐩)
    where the entries in row i are the heights of the east-steps of pᵢ.

    Moreover, the weight of a nipat equals the monomial x_T of the
    corresponding tableau. -/
lemma nipat_ssyt_bijection (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    ∃ f : Nipat lam mu hlam hmu hcontained →
        SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩,
      Function.Bijective f ∧
      ∀ np, np.weight (R := R) = (f np).toMonomial := by
  use nipatToSSYT
  constructor
  · -- Prove bijectivity using ssytToNipat as the inverse
    constructor
    · -- Injective: if nipatToSSYT np1 = nipatToSSYT np2, then np1 = np2
      intro np1 np2 h
      rw [← ssytToNipat_nipatToSSYT np1, ← ssytToNipat_nipatToSSYT np2, h]
    · -- Surjective: for any T, there exists np such that nipatToSSYT np = T
      intro T
      use ssytToNipat T
      exact nipatToSSYT_ssytToNipat T
  · -- Weight preservation
    exact nipatToSSYT_weight

/-- The sum of nipat weights equals the sum of SSYT monomials.
    This follows from the bijection and weight preservation. -/
lemma nipatWeightSum_eq_ssytSum (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    ∑ np : Nipat lam mu hlam hmu hcontained, np.weight (R := R) =
      ∑ T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩, T.toMonomial := by
  -- Use the equivalence nipatSSYTEquiv to rewrite the sum
  -- The key facts are:
  -- 1. nipatSSYTEquiv is an equivalence (bijection)
  -- 2. nipatToSSYT_weight: np.weight = (nipatToSSYT np).toMonomial
  -- The proof follows by Equiv.sum_comp
  let e := nipatSSYTEquiv lam mu hlam hmu hcontained
  have h1 : ∀ np, np.weight (R := R) = (e np).toMonomial := nipatToSSYT_weight
  simp_rw [h1]
  exact Equiv.sum_comp e (fun T => T.toMonomial)

/-- The sum of nipat weights equals skewSchur.
    This combines the bijection with the definition of skewSchur. -/
lemma nipatWeightSum_eq_skewSchur (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    ∑ np : Nipat lam mu hlam hmu hcontained, np.weight (R := R) =
      skewSchur (R := R) ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ := by
  rw [nipatWeightSum_eq_ssytSum]
  -- skewSchur is defined as ∑ T ∈ skewSSYTFinset s, T.toMonomial
  -- We need to show this equals ∑ T : SkewSSYT s, T.toMonomial
  unfold skewSchur
  -- The sum over skewSSYTFinset equals the sum over all SkewSSYT
  symm
  apply Finset.sum_bij (fun T _ => T)
  · intro T _; exact Finset.mem_univ T
  · intro T₁ _ T₂ _ h; exact h
  · intro T _; exact ⟨T, skewSSYTFinset_mem _ T, rfl⟩
  · intro T _; rfl

/-- The source vertices have x-coordinates that are weakly decreasing. -/
lemma jacobiTrudiSourceVertex_xDecreasing (mu : Fin N → ℕ)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i) :
    LGV.xDecreasing (jacobiTrudiSourceVertex mu) := by
  intro i j hij
  simp only [LGV.xCoord, jacobiTrudiSourceVertex]
  exact jacobiTrudiSourceX_antitone mu hmu i j hij

/-- The source vertices have y-coordinates that are constant (trivially increasing). -/
lemma jacobiTrudiSourceVertex_yIncreasing (mu : Fin N → ℕ) :
    LGV.yIncreasing (jacobiTrudiSourceVertex mu) := by
  intro i j _
  simp only [LGV.yCoord, jacobiTrudiSourceVertex, le_refl]

/-- The target vertices have x-coordinates that are weakly decreasing. -/
lemma jacobiTrudiTargetVertex_xDecreasing (lam : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
    LGV.xDecreasing (jacobiTrudiTargetVertex lam) := by
  intro i j hij
  simp only [LGV.xCoord, jacobiTrudiTargetVertex]
  exact jacobiTrudiTargetX_antitone lam hlam i j hij

/-- The target vertices have y-coordinates that are constant (trivially increasing). -/
lemma jacobiTrudiTargetVertex_yIncreasing (lam : Fin N → ℕ) :
    LGV.yIncreasing (jacobiTrudiTargetVertex lam) := by
  intro i j _
  simp only [LGV.yCoord, jacobiTrudiTargetVertex, le_refl]

/-- All y-coordinates in the east-step list are ≥ the starting y-coordinate.
    This is a key lemma for proving uniqueness of paths from east-step coordinates. -/
lemma lgvPathEastStepYCoords_ge_start (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (y : ℤ) (hy : y ∈ lgvPathEastStepYCoords vertices) :
    (vertices.head h_ne).2 ≤ y := by
  match vertices with
  | [] => simp at h_ne
  | [v] => simp [lgvPathEastStepYCoords] at hy
  | v₀ :: v₁ :: rest =>
    simp only [lgvPathEastStepYCoords] at hy
    have h_arc : LGV.integerLattice.arc v₀ v₁ := by
      have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
      simp at this; exact this
    have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
        LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
          ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
      intro i hi
      have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
      exact h_arcs (i + 1) hi'
    split_ifs at hy with h_east
    · simp only [List.mem_cons] at hy
      rcases hy with rfl | hy'
      · simp [List.head_cons]
      · have ih := lgvPathEastStepYCoords_ge_start (v₁ :: rest) (List.cons_ne_nil _ _) h_arcs' y hy'
        simp only [List.head_cons] at ih ⊢
        have hv01 : v₀.2 = v₁.2 := h_east.2.symm
        omega
    · have ih := lgvPathEastStepYCoords_ge_start (v₁ :: rest) (List.cons_ne_nil _ _) h_arcs' y hy
      simp only [List.head_cons] at ih ⊢
      rcases h_arc with ⟨hx, hy_eq⟩ | ⟨hx, hy_eq⟩
      · exfalso; apply h_east; exact ⟨hx, hy_eq⟩
      · omega

/-- Helper: if the first east-step y-coord exists, it is ≥ start.2.
    This is because y-coords are non-decreasing along the path. -/
lemma lgvPathEastStepYCoords_head_ge_start (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (y : ℤ) (hy : y ∈ (lgvPathEastStepYCoords vertices).head?) :
    (vertices.head h_ne).2 ≤ y := by
  cases vertices with
  | nil => exact absurd rfl h_ne
  | cons v₀ tl =>
    cases tl with
    | nil => simp [lgvPathEastStepYCoords] at hy
    | cons v₁ rest =>
      simp only [lgvPathEastStepYCoords, List.head_cons] at hy ⊢
      split_ifs at hy with h_east
      · simp at hy; omega
      · have h_arc : LGV.integerLattice.arc v₀ v₁ := by
          have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
          simp at this; exact this
        have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
            LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
          have := h_arcs (i + 1) hi'
          simp at this ⊢; exact this
        have h_ne' : v₁ :: rest ≠ [] := List.cons_ne_nil v₁ rest
        have hv1_le_y := lgvPathEastStepYCoords_head_ge_start (v₁ :: rest) h_ne' h_arcs' y hy
        simp only [List.head_cons] at hv1_le_y
        simp only [LGV.integerLattice] at h_arc
        rcases h_arc with ⟨hx, hvy⟩ | ⟨_, hvy⟩
        · exfalso; apply h_east; exact ⟨hx, hvy⟩
        · omega
termination_by vertices.length

/-- The k-th element of lgvYCoordsToFinN equals (ycoords[k] - 1).toNat.
    Since ycoords[k] ∈ [1, N], we have (lgvYCoordsToFinN ycoords h)[k].val + 1 = ycoords[k]. -/
lemma lgvYCoordsToFinN_getElem (ycoords : List ℤ) (h : ∀ y ∈ ycoords, 1 ≤ y ∧ y ≤ N)
    (k : ℕ) (hk : k < ycoords.length)
    (hk' : k < (lgvYCoordsToFinN ycoords h).length := by rw [lgvYCoordsToFinN_length]; exact hk) :
    ((lgvYCoordsToFinN ycoords h)[k]).val + 1 = ycoords[k] := by
  simp only [lgvYCoordsToFinN, List.getElem_pmap]
  have hmem : ycoords[k] ∈ ycoords := List.getElem_mem hk
  have hbnd := h _ hmem
  omega

/-- The conversion lgvYCoordsToFinN is injective when both lists have elements in [1, N].

    The proof uses the fact that y ↦ (y - 1).toNat is injective on [1, N]:
    if (y₁ - 1).toNat = (y₂ - 1).toNat and both y₁, y₂ ∈ [1, N], then y₁ = y₂.

    **Proof sketch:**
    1. The lengths are equal (pmap preserves length)
    2. At each position i, the Fin N values are equal (from heq)
    3. Since y ↦ (y - 1).toNat is injective on [1, N], the original values are equal -/
lemma lgvYCoordsToFinN_injective (l₁ l₂ : List ℤ)
    (h₁ : ∀ y ∈ l₁, 1 ≤ y ∧ y ≤ N) (h₂ : ∀ y ∈ l₂, 1 ≤ y ∧ y ≤ N)
    (heq : lgvYCoordsToFinN l₁ h₁ = lgvYCoordsToFinN l₂ h₂) : l₁ = l₂ := by
  -- First show lengths are equal
  have hlen : l₁.length = l₂.length := by
    have := congrArg List.length heq
    simp only [lgvYCoordsToFinN, List.length_pmap] at this
    exact this
  -- Then show elements are equal at each position
  apply List.ext_get hlen
  intro i hi₁ hi₂
  -- From heq, the i-th Fin N values are equal
  have hmem₁ : l₁[i] ∈ l₁ := List.getElem_mem hi₁
  have hmem₂ : l₂[i] ∈ l₂ := List.getElem_mem hi₂
  have h1i := h₁ _ hmem₁
  have h2i := h₂ _ hmem₂
  -- Extract the equality of Fin N values at position i
  have hi₁' : i < (lgvYCoordsToFinN l₁ h₁).length := by
    simp only [lgvYCoordsToFinN, List.length_pmap]
    exact hi₁
  have hi₂' : i < (lgvYCoordsToFinN l₂ h₂).length := by
    simp only [lgvYCoordsToFinN, List.length_pmap]
    exact hi₂
  have heq_i : (lgvYCoordsToFinN l₁ h₁)[i]'hi₁' = (lgvYCoordsToFinN l₂ h₂)[i]'hi₂' := by
    simp only [heq]
  -- Use getElem_pmap to relate the pmap values to the original list values
  simp only [lgvYCoordsToFinN] at heq_i
  rw [List.getElem_pmap, List.getElem_pmap] at heq_i
  -- heq_i now says the Fin N values are equal
  simp only [Fin.mk.injEq] at heq_i
  -- heq_i : (l₁[i] - 1).toNat = (l₂[i] - 1).toNat
  -- Since both are in [1, N], this implies l₁[i] = l₂[i]
  have h1 : 0 ≤ l₁[i] - 1 := by omega
  have h2 : 0 ≤ l₂[i] - 1 := by omega
  have ha' := Int.toNat_of_nonneg h1
  have hb' := Int.toNat_of_nonneg h2
  simp only [List.get_eq_getElem]
  omega

/-- Helper: lgvYCoordsToFinN inverts the map (fun h => h.val + 1).
    If `l = heights.map (fun h => h.val + 1)`, then `lgvYCoordsToFinN l h = heights`. -/
lemma lgvYCoordsToFinN_map_val_add_one_eq (heights : List (Fin N)) {l : List ℤ}
    (heq : l = heights.map (fun h => (h.val : ℤ) + 1))
    (h : ∀ y ∈ l, 1 ≤ y ∧ y ≤ N) :
    lgvYCoordsToFinN l h = heights := by
  subst heq
  unfold lgvYCoordsToFinN
  apply List.ext_getElem
  · simp [List.length_pmap]
  · intro i hi₁ hi₂
    simp only [List.getElem_pmap, List.getElem_map, Fin.ext_iff]
    have : (((heights[i]).val : ℤ) + 1 - 1).toNat = (heights[i]).val := by omega
    exact this

/-- Coordinate sum strictly increases along arcs in the integer lattice. -/
lemma coordSum_strict_inc (u v : ℤ × ℤ) (h : LGV.integerLattice.arc u v) :
    u.1 + u.2 < v.1 + v.2 := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega

/-- Coordinate sum is monotone along paths in the integer lattice. -/
lemma coordSum_head_le_last (vertices : List (ℤ × ℤ)) (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)) :
    (vertices.head h_ne).1 + (vertices.head h_ne).2 ≤
    (vertices.getLast h_ne).1 + (vertices.getLast h_ne).2 := by
  match vertices with
  | [] => simp at h_ne
  | [v] => simp
  | v₀ :: v₁ :: rest =>
    have h_arc : LGV.integerLattice.arc v₀ v₁ := by
      have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
      simp at this; exact this
    have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
        LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
          ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
      intro i hi
      have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
      exact h_arcs (i + 1) hi'
    have ih := coordSum_head_le_last (v₁ :: rest) (List.cons_ne_nil _ _) h_arcs'
    simp only [List.head_cons, List.getLast_cons (List.cons_ne_nil _ _)] at ih ⊢
    have hstep := coordSum_strict_inc v₀ v₁ h_arc
    omega

/-- Coordinate sum strictly increases for paths of length ≥ 2. -/
lemma coordSum_head_lt_last_of_length_ge_two (vertices : List (ℤ × ℤ)) (h_ne : vertices ≠ [])
    (h_len : vertices.length ≥ 2)
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)) :
    (vertices.head h_ne).1 + (vertices.head h_ne).2 <
    (vertices.getLast h_ne).1 + (vertices.getLast h_ne).2 := by
  match vertices with
  | [] => simp at h_ne
  | [v] => simp at h_len
  | v₀ :: v₁ :: rest =>
    have h_arc : LGV.integerLattice.arc v₀ v₁ := by
      have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
      simp at this; exact this
    have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
        LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
          ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
      intro i hi
      have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
      exact h_arcs (i + 1) hi'
    have ih := coordSum_head_le_last (v₁ :: rest) (List.cons_ne_nil _ _) h_arcs'
    simp only [List.head_cons, List.getLast_cons (List.cons_ne_nil _ _)] at ih ⊢
    have hstep := coordSum_strict_inc v₀ v₁ h_arc
    omega

/-- Auxiliary lemma for lgvPath_vertices_eq_of_eastStepYCoords_eq. -/
lemma lgvPath_vertices_eq_aux (vs₁ vs₂ : List (ℤ × ℤ))
    (h_ne₁ : vs₁ ≠ []) (h_ne₂ : vs₂ ≠ [])
    (h_arcs₁ : ∀ i : ℕ, ∀ hi : i + 1 < vs₁.length,
      LGV.integerLattice.arc (vs₁.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vs₁.get ⟨i + 1, hi⟩))
    (h_arcs₂ : ∀ i : ℕ, ∀ hi : i + 1 < vs₂.length,
      LGV.integerLattice.arc (vs₂.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vs₂.get ⟨i + 1, hi⟩))
    (hstart : vs₁.head h_ne₁ = vs₂.head h_ne₂)
    (hfinish : vs₁.getLast h_ne₁ = vs₂.getLast h_ne₂)
    (hcoords : lgvPathEastStepYCoords vs₁ = lgvPathEastStepYCoords vs₂) :
    vs₁ = vs₂ := by
  induction h : vs₁.length + vs₂.length using Nat.strong_induction_on generalizing vs₁ vs₂ with
  | _ n ih =>
    match hvs₁ : vs₁, hvs₂ : vs₂ with
    | [v₁], [v₂] =>
      simp only [List.head_cons] at hstart
      rw [hstart]
    | [v₁], v₂ :: w₂ :: rest₂ =>
      exfalso
      simp only [List.head_cons, List.getLast_singleton] at hstart hfinish
      have h_len : (v₂ :: w₂ :: rest₂).length ≥ 2 := by simp
      have hlt := coordSum_head_lt_last_of_length_ge_two (v₂ :: w₂ :: rest₂)
        (List.cons_ne_nil _ _) h_len h_arcs₂
      simp only [List.head_cons] at hlt
      have hlast_eq : (v₂ :: w₂ :: rest₂).getLast (List.cons_ne_nil _ _) = v₁ := hfinish.symm
      have hcontra : v₂.1 + v₂.2 < v₂.1 + v₂.2 :=
        calc v₂.1 + v₂.2 < ((v₂ :: w₂ :: rest₂).getLast _).1 + ((v₂ :: w₂ :: rest₂).getLast _).2 := hlt
          _ = v₁.1 + v₁.2 := by rw [hlast_eq]
          _ = v₂.1 + v₂.2 := by rw [hstart]
      omega
    | v₁ :: w₁ :: rest₁, [v₂] =>
      exfalso
      simp only [List.head_cons, List.getLast_singleton] at hstart hfinish
      have h_len : (v₁ :: w₁ :: rest₁).length ≥ 2 := by simp
      have hlt := coordSum_head_lt_last_of_length_ge_two (v₁ :: w₁ :: rest₁)
        (List.cons_ne_nil _ _) h_len h_arcs₁
      simp only [List.head_cons] at hlt
      have hlast_eq : (v₁ :: w₁ :: rest₁).getLast (List.cons_ne_nil _ _) = v₂ := hfinish
      have hcontra : v₁.1 + v₁.2 < v₁.1 + v₁.2 :=
        calc v₁.1 + v₁.2 < ((v₁ :: w₁ :: rest₁).getLast _).1 + ((v₁ :: w₁ :: rest₁).getLast _).2 := hlt
          _ = v₂.1 + v₂.2 := by rw [hlast_eq]
          _ = v₁.1 + v₁.2 := by rw [← hstart]
      omega
    | v₁ :: w₁ :: rest₁, v₂ :: w₂ :: rest₂ =>
      simp only [List.head_cons] at hstart
      have h_arc₁ : LGV.integerLattice.arc v₁ w₁ := by
        have := h_arcs₁ 0 (by simp : 0 + 1 < (v₁ :: w₁ :: rest₁).length)
        simp at this; exact this
      have h_arc₂ : LGV.integerLattice.arc v₂ w₂ := by
        have := h_arcs₂ 0 (by simp : 0 + 1 < (v₂ :: w₂ :: rest₂).length)
        simp at this; exact this
      rcases h_arc₁ with ⟨hx₁, hy₁⟩ | ⟨hx₁, hy₁⟩ <;>
      rcases h_arc₂ with ⟨hx₂, hy₂⟩ | ⟨hx₂, hy₂⟩
      · -- Both east steps
        have hw_eq : w₁ = w₂ := by
          ext
          · rw [hx₁, hx₂]; congr 1; exact congrArg Prod.fst hstart
          · rw [hy₁, hy₂]; exact congrArg Prod.snd hstart
        have h_arcs₁' : ∀ i : ℕ, ∀ hi : i + 1 < (w₁ :: rest₁).length,
            LGV.integerLattice.arc ((w₁ :: rest₁).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((w₁ :: rest₁).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₁ :: w₁ :: rest₁).length := by simp at hi ⊢; omega
          exact h_arcs₁ (i + 1) hi'
        have h_arcs₂' : ∀ i : ℕ, ∀ hi : i + 1 < (w₂ :: rest₂).length,
            LGV.integerLattice.arc ((w₂ :: rest₂).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((w₂ :: rest₂).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₂ :: w₂ :: rest₂).length := by simp at hi ⊢; omega
          exact h_arcs₂ (i + 1) hi'
        have hstart' : (w₁ :: rest₁).head (List.cons_ne_nil _ _) =
            (w₂ :: rest₂).head (List.cons_ne_nil _ _) := hw_eq
        have hfinish' : (w₁ :: rest₁).getLast (List.cons_ne_nil _ _) =
            (w₂ :: rest₂).getLast (List.cons_ne_nil _ _) := by
          rw [← List.getLast_cons (List.cons_ne_nil w₁ rest₁),
              ← List.getLast_cons (List.cons_ne_nil w₂ rest₂)]
          exact hfinish
        have hcoords' : lgvPathEastStepYCoords (w₁ :: rest₁) =
            lgvPathEastStepYCoords (w₂ :: rest₂) := by
          simp only [lgvPathEastStepYCoords, hx₁, hy₁, hx₂, hy₂, and_self, ↓reduceIte] at hcoords
          exact (List.cons_eq_cons.mp hcoords).2
        have hlen : (w₁ :: rest₁).length + (w₂ :: rest₂).length < n := by
          simp only [List.length_cons] at h ⊢; omega
        have ih_result := ih ((w₁ :: rest₁).length + (w₂ :: rest₂).length) hlen
            (w₁ :: rest₁) (w₂ :: rest₂)
            (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
            h_arcs₁' h_arcs₂' hstart' hfinish' hcoords' rfl
        rw [List.cons_eq_cons, List.cons_eq_cons]
        exact ⟨hstart, List.cons_eq_cons.mp ih_result⟩
      · -- First east, second north: contradiction
        exfalso
        simp only [lgvPathEastStepYCoords, hx₁, hy₁, and_self, ↓reduceIte] at hcoords
        have h_not_cond₂ : ¬(w₂.1 = v₂.1 + 1 ∧ w₂.2 = v₂.2) := by omega
        simp only [h_not_cond₂, ↓reduceIte] at hcoords
        have h_arcs₂' : ∀ i : ℕ, ∀ hi : i + 1 < (w₂ :: rest₂).length,
            LGV.integerLattice.arc ((w₂ :: rest₂).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((w₂ :: rest₂).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₂ :: w₂ :: rest₂).length := by simp at hi ⊢; omega
          exact h_arcs₂ (i + 1) hi'
        cases h_rhs : lgvPathEastStepYCoords (w₂ :: rest₂) with
        | nil => rw [h_rhs] at hcoords; exact List.cons_ne_nil _ _ hcoords
        | cons y ys =>
          rw [h_rhs] at hcoords
          have h_y_eq : v₁.2 = y := (List.cons_eq_cons.mp hcoords).1
          have hmem : y ∈ lgvPathEastStepYCoords (w₂ :: rest₂) := by
            rw [h_rhs]; exact List.Mem.head _
          have h_y_ge := lgvPathEastStepYCoords_ge_start (w₂ :: rest₂)
              (List.cons_ne_nil _ _) h_arcs₂' y hmem
          simp only [List.head_cons] at h_y_ge
          have hw2_y : w₂.2 = v₁.2 + 1 := by
            rw [hy₂]; exact congrArg (· + 1) (congrArg Prod.snd hstart.symm)
          omega
      · -- First north, second east: contradiction
        exfalso
        simp only [lgvPathEastStepYCoords, hx₂, hy₂, and_self, ↓reduceIte] at hcoords
        have h_not_cond₁ : ¬(w₁.1 = v₁.1 + 1 ∧ w₁.2 = v₁.2) := by omega
        simp only [h_not_cond₁, ↓reduceIte] at hcoords
        have h_arcs₁' : ∀ i : ℕ, ∀ hi : i + 1 < (w₁ :: rest₁).length,
            LGV.integerLattice.arc ((w₁ :: rest₁).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((w₁ :: rest₁).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₁ :: w₁ :: rest₁).length := by simp at hi ⊢; omega
          exact h_arcs₁ (i + 1) hi'
        cases h_lhs : lgvPathEastStepYCoords (w₁ :: rest₁) with
        | nil => rw [h_lhs] at hcoords; exact List.cons_ne_nil _ _ hcoords.symm
        | cons y ys =>
          rw [h_lhs] at hcoords
          have h_y_eq : y = v₂.2 := (List.cons_eq_cons.mp hcoords.symm).1.symm
          have hmem : y ∈ lgvPathEastStepYCoords (w₁ :: rest₁) := by
            rw [h_lhs]; exact List.Mem.head _
          have h_y_ge := lgvPathEastStepYCoords_ge_start (w₁ :: rest₁)
              (List.cons_ne_nil _ _) h_arcs₁' y hmem
          simp only [List.head_cons] at h_y_ge
          have hw1_y : w₁.2 = v₂.2 + 1 := by
            rw [hy₁]; exact congrArg (· + 1) (congrArg Prod.snd hstart)
          omega
      · -- Both north steps
        have hw_eq : w₁ = w₂ := by
          ext
          · rw [hx₁, hx₂]; exact congrArg Prod.fst hstart
          · rw [hy₁, hy₂]; exact congrArg (· + 1) (congrArg Prod.snd hstart)
        have h_arcs₁' : ∀ i : ℕ, ∀ hi : i + 1 < (w₁ :: rest₁).length,
            LGV.integerLattice.arc ((w₁ :: rest₁).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((w₁ :: rest₁).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₁ :: w₁ :: rest₁).length := by simp at hi ⊢; omega
          exact h_arcs₁ (i + 1) hi'
        have h_arcs₂' : ∀ i : ℕ, ∀ hi : i + 1 < (w₂ :: rest₂).length,
            LGV.integerLattice.arc ((w₂ :: rest₂).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((w₂ :: rest₂).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₂ :: w₂ :: rest₂).length := by simp at hi ⊢; omega
          exact h_arcs₂ (i + 1) hi'
        have hstart' : (w₁ :: rest₁).head (List.cons_ne_nil _ _) =
            (w₂ :: rest₂).head (List.cons_ne_nil _ _) := hw_eq
        have hfinish' : (w₁ :: rest₁).getLast (List.cons_ne_nil _ _) =
            (w₂ :: rest₂).getLast (List.cons_ne_nil _ _) := by
          rw [← List.getLast_cons (List.cons_ne_nil w₁ rest₁),
              ← List.getLast_cons (List.cons_ne_nil w₂ rest₂)]
          exact hfinish
        have hcoords' : lgvPathEastStepYCoords (w₁ :: rest₁) =
            lgvPathEastStepYCoords (w₂ :: rest₂) := by
          simp only [lgvPathEastStepYCoords] at hcoords
          have h_not_cond₁ : ¬(w₁.1 = v₁.1 + 1 ∧ w₁.2 = v₁.2) := by omega
          have h_not_cond₂ : ¬(w₂.1 = v₂.1 + 1 ∧ w₂.2 = v₂.2) := by omega
          simp only [h_not_cond₁, h_not_cond₂, ↓reduceIte] at hcoords
          exact hcoords
        have hlen : (w₁ :: rest₁).length + (w₂ :: rest₂).length < n := by
          simp only [List.length_cons] at h ⊢; omega
        have ih_result := ih ((w₁ :: rest₁).length + (w₂ :: rest₂).length) hlen
            (w₁ :: rest₁) (w₂ :: rest₂)
            (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
            h_arcs₁' h_arcs₂' hstart' hfinish' hcoords' rfl
        rw [List.cons_eq_cons, List.cons_eq_cons]
        exact ⟨hstart, List.cons_eq_cons.mp ih_result⟩


/-- Key uniqueness lemma: Paths in the integer lattice from the same start to the same end
    with the same east-step y-coordinates must have the same vertices.

    This is the fundamental lemma for proving injectivity of `lgvPathToLatticePath`.

    **Proof idea**: At each vertex (x, y), the next step is uniquely determined:
    - If y appears in the remaining east-step y-coordinates, we go east
    - Otherwise, we go north
    Since both paths have the same start and the same east-step y-coordinates,
    they must make the same choices at each step, hence have the same vertices.

    The proof proceeds by strong induction on the total number of steps remaining.
    At each step, we show the next vertex is determined by whether the current
    y-coordinate matches the next east-step height. -/
lemma lgvPath_vertices_eq_of_eastStepYCoords_eq
    (p₁ p₂ : LGV.SimpleDigraph.Path LGV.integerLattice)
    (hstart : p₁.start = p₂.start)
    (hfinish : p₁.finish = p₂.finish)
    (hcoords : lgvPathEastStepYCoords p₁.vertices = lgvPathEastStepYCoords p₂.vertices) :
    p₁.vertices = p₂.vertices :=
  lgvPath_vertices_eq_aux p₁.vertices p₂.vertices p₁.nonempty p₂.nonempty
    p₁.arcs_valid p₂.arcs_valid hstart hfinish hcoords

/-- Corollary: lgvPathToLatticePath is injective on paths with the same start and end.

    If two LGV paths from (a, 1) to (c, N) map to the same LatticePath,
    then they have the same vertices (and hence are equal as paths). -/
lemma lgvPathToLatticePath_injective (a c : ℤ)
    (p₁ p₂ : LGV.SimpleDigraph.Path LGV.integerLattice)
    (hstart₁ : p₁.start = (a, 1)) (hfinish₁ : p₁.finish = (c, (N : ℤ)))
    (hstart₂ : p₂.start = (a, 1)) (hfinish₂ : p₂.finish = (c, (N : ℤ)))
    (heq : lgvPathToLatticePath a c p₁ hstart₁ hfinish₁ =
           lgvPathToLatticePath a c p₂ hstart₂ hfinish₂) :
    p₁ = p₂ := by
  -- The LatticePaths are equal iff their eastStepHeights are equal.
  -- eastStepHeights = lgvYCoordsToFinN (lgvPathEastStepYCoords vertices) ...
  -- Since lgvYCoordsToFinN is injective (it's a pmap that preserves the list structure),
  -- equal eastStepHeights implies equal lgvPathEastStepYCoords.
  -- By lgvPath_vertices_eq_of_eastStepYCoords_eq, the paths have the same vertices.
  -- Paths with the same vertices are equal.
  have hcoords : lgvPathEastStepYCoords p₁.vertices = lgvPathEastStepYCoords p₂.vertices := by
    -- Extract from heq that the eastStepHeights are equal
    have h := congrArg LatticePath.eastStepHeights heq
    simp only [lgvPathToLatticePath] at h
    -- Use lgvYCoordsToFinN_injective to conclude the y-coordinates are equal
    have hbnd₁ : ∀ y ∈ lgvPathEastStepYCoords p₁.vertices, 1 ≤ y ∧ y ≤ N := by
      intro y hy
      have hbnd := lgvPathEastStepYCoords_bounded p₁.vertices p₁.nonempty p₁.arcs_valid y hy
      simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at hstart₁ hfinish₁
      rw [hstart₁, hfinish₁] at hbnd
      simp at hbnd
      exact hbnd
    have hbnd₂ : ∀ y ∈ lgvPathEastStepYCoords p₂.vertices, 1 ≤ y ∧ y ≤ N := by
      intro y hy
      have hbnd := lgvPathEastStepYCoords_bounded p₂.vertices p₂.nonempty p₂.arcs_valid y hy
      simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at hstart₂ hfinish₂
      rw [hstart₂, hfinish₂] at hbnd
      simp at hbnd
      exact hbnd
    exact lgvYCoordsToFinN_injective _ _ hbnd₁ hbnd₂ h
  have hstart : p₁.start = p₂.start := by rw [hstart₁, hstart₂]
  have hfinish : p₁.finish = p₂.finish := by rw [hfinish₁, hfinish₂]
  have hvertices := lgvPath_vertices_eq_of_eastStepYCoords_eq p₁ p₂ hstart hfinish hcoords
  -- Two paths are equal iff their vertices are equal
  cases p₁; cases p₂
  simp only [LGV.SimpleDigraph.Path.mk.injEq] at hvertices ⊢
  exact hvertices

/-- The vertices built by buildVerticesAux are never empty. -/
lemma buildVerticesAux_nonempty (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ) :
    buildVerticesAux N x y heights fuel ≠ [] := by
  induction fuel generalizing x y heights with
  | zero => simp [buildVerticesAux]
  | succ n ih =>
    simp only [buildVerticesAux]
    cases heights with
    | nil => split_ifs <;> simp
    | cons h rest => simp only [ne_eq]; split_ifs <;> simp

/-- The vertices built by buildVertices are never empty. -/
lemma buildVertices_nonempty (a c : ℤ) (N : ℕ) (eastStepHeights : List (Fin N)) :
    buildVertices a c N eastStepHeights ≠ [] := by
  simp only [buildVertices]
  exact buildVerticesAux_nonempty N a 1 eastStepHeights _

/-- The first vertex built by buildVerticesAux is (x, y). -/
lemma buildVerticesAux_head (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (hfuel : fuel ≥ 1 ∨ heights = []) :
    (buildVerticesAux N x y heights fuel).head (buildVerticesAux_nonempty N x y heights fuel) = (x, y) := by
  cases fuel with
  | zero => simp [buildVerticesAux]
  | succ n =>
    simp only [buildVerticesAux]
    cases heights with
    | nil => split_ifs <;> simp
    | cons h rest => simp only; split_ifs with h1 <;> simp

/-- The first vertex built by buildVertices is (a, 1) when N ≥ 1. -/
lemma buildVertices_head (a c : ℤ) (N : ℕ) (eastStepHeights : List (Fin N)) (hN : N ≥ 1) :
    (buildVertices a c N eastStepHeights).head (buildVertices_nonempty a c N eastStepHeights) = (a, 1) := by
  simp only [buildVertices]
  apply buildVerticesAux_head
  left
  omega
/-- Helper: get the first element of buildVerticesAux using array notation. -/
lemma buildVerticesAux_head_getElem (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (h : 0 < (buildVerticesAux N x y heights fuel).length) :
    (buildVerticesAux N x y heights fuel)[0] = (x, y) := by
  cases fuel with
  | zero => simp [buildVerticesAux]
  | succ n =>
    cases heights with
    | nil =>
      simp only [buildVerticesAux]
      split_ifs <;> simp
    | cons hd rest =>
      simp only [buildVerticesAux]
      split_ifs <;> simp

/-- Helper: the length of buildVerticesAux is at least 1. -/
lemma buildVerticesAux_length_pos (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ) :
    0 < (buildVerticesAux N x y heights fuel).length :=
  List.length_pos_of_ne_nil (buildVerticesAux_nonempty N x y heights fuel)

/-- All x-coordinates in buildVerticesAux are ≥ the starting x-coordinate.
    This is because we only move north (same x) or east (x + 1). -/
lemma buildVerticesAux_x_ge (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (idx : ℕ) (hidx : idx < (buildVerticesAux N x y heights fuel).length) :
    (buildVerticesAux N x y heights fuel)[idx].1 ≥ x := by
  induction fuel generalizing x y heights idx with
  | zero =>
    simp only [buildVerticesAux, List.length_singleton] at hidx
    have : idx = 0 := by omega
    subst this
    simp only [buildVerticesAux, List.getElem_singleton, ge_iff_le, le_refl]
  | succ n ih =>
    cases heights with
    | nil =>
      simp only [buildVerticesAux] at hidx ⊢
      split_ifs at hidx ⊢ with hy_lt
      · cases idx with
        | zero =>
          simp only [List.getElem_cons_zero, ge_iff_le, le_refl]
        | succ idx' =>
          have hidx' : idx' < (buildVerticesAux N x (y + 1) [] n).length := by
            simp only [List.length_cons] at hidx; omega
          have hih := ih x (y + 1) [] idx' hidx'
          simp only [ge_iff_le, List.getElem_cons_succ] at hih ⊢
          exact hih
      · simp only [List.length_singleton] at hidx
        have : idx = 0 := by omega
        subst this
        simp only [List.getElem_singleton, ge_iff_le, le_refl]
    | cons h rest =>
      simp only [buildVerticesAux] at hidx ⊢
      split_ifs at hidx ⊢ with hy_lt
      · cases idx with
        | zero =>
          simp only [List.getElem_cons_zero, ge_iff_le, le_refl]
        | succ idx' =>
          have hidx' : idx' < (buildVerticesAux N x (y + 1) (h :: rest) n).length := by
            simp only [List.length_cons] at hidx; omega
          have hih := ih x (y + 1) (h :: rest) idx' hidx'
          simp only [ge_iff_le, List.getElem_cons_succ] at hih ⊢
          exact hih
      · cases idx with
        | zero =>
          simp only [List.getElem_cons_zero, ge_iff_le, le_refl]
        | succ idx' =>
          have hidx' : idx' < (buildVerticesAux N (x + 1) y rest n).length := by
            simp only [List.length_cons] at hidx; omega
          have hge := ih (x + 1) y rest idx' hidx'
          simp only [ge_iff_le, List.getElem_cons_succ] at hge ⊢
          omega

/-- Y-coordinate upper bound invariant for buildVerticesAux.
    At x-coordinate x + j (after j east steps), the y-coordinate is at most heights[j].val + 1.
    This is because we haven't made the j-th east step yet. -/
lemma buildVerticesAux_y_upper_bound (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (hfuel : fuel ≥ heights.length + (N - y.toNat)) (hy : 1 ≤ y) (hyN : y ≤ N)
    (hchain : heights.IsChain (· ≤ ·))
    (hbounds : ∀ h ∈ heights, y ≤ (h.val : ℤ) + 1)
    (idx : ℕ) (hidx : idx < (buildVerticesAux N x y heights fuel).length)
    (j : ℕ) (hj : j < heights.length)
    (hx_eq : (buildVerticesAux N x y heights fuel)[idx].1 = x + j) :
    (buildVerticesAux N x y heights fuel)[idx].2 ≤ (heights[j]).val + 1 := by
  induction fuel generalizing x y heights idx j with
  | zero =>
    simp only [buildVerticesAux, List.length_singleton] at hidx
    have hidx_eq : idx = 0 := by omega
    subst hidx_eq
    simp only [buildVerticesAux, List.getElem_singleton] at hx_eq ⊢
    have hj_eq : j = 0 := by omega
    subst hj_eq
    have h0 : heights[0] ∈ heights := List.getElem_mem hj
    exact hbounds heights[0] h0
  | succ n ih =>
    cases heights with
    | nil => simp at hj
    | cons h rest =>
      simp only [buildVerticesAux] at hidx hx_eq ⊢
      split_ifs at hidx hx_eq ⊢ with hy_lt
      · -- North case: y < h.val + 1
        cases idx with
        | zero =>
          simp only [List.getElem_cons_zero] at hx_eq ⊢
          have hj_eq : j = 0 := by omega
          subst hj_eq
          simp only [List.getElem_cons_zero]
          omega
        | succ idx' =>
          simp only [List.length_cons] at hidx
          have hidx' : idx' < (buildVerticesAux N x (y + 1) (h :: rest) n).length := by omega
          simp only [List.getElem_cons_succ] at hx_eq ⊢
          have hfuel' : n ≥ (h :: rest).length + (N - (y + 1).toNat) := by
            simp only [List.length_cons] at hfuel ⊢
            have hy_pos : 0 ≤ y := by omega
            have h1 : (y + 1).toNat = y.toNat + 1 := by omega
            rw [h1]
            have hle : y.toNat < N := by
              have hh := h.isLt
              have hthis : y < N := by omega
              have htonat : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy_pos
              omega
            omega
          have hbounds' : ∀ h' ∈ (h :: rest), (y + 1) ≤ (h'.val : ℤ) + 1 := by
            intro h' hmem
            cases List.mem_cons.mp hmem with
            | inl heq => subst heq; omega
            | inr hrest =>
              have hrel : h ≤ h' := hchain.rel_cons hrest
              have hval : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
              omega
          have hyN' : y + 1 ≤ N := by
            have hh := h.isLt
            have hb := hbounds h List.mem_cons_self
            omega
          exact ih x (y + 1) (h :: rest) hfuel' (by omega) hyN' hchain hbounds' idx' hidx' j hj hx_eq
      · -- East case: y ≥ h.val + 1
        cases idx with
        | zero =>
          simp only [List.getElem_cons_zero] at hx_eq ⊢
          have hj_eq : j = 0 := by omega
          subst hj_eq
          simp only [List.getElem_cons_zero]
          have hb := hbounds h List.mem_cons_self
          omega
        | succ idx' =>
          simp only [List.length_cons] at hidx
          have hidx' : idx' < (buildVerticesAux N (x + 1) y rest n).length := by omega
          simp only [List.getElem_cons_succ] at hx_eq ⊢
          have hx_ge := buildVerticesAux_x_ge N (x + 1) y rest n idx' hidx'
          have hj_pos : j ≥ 1 := by omega
          have hj' : j - 1 < rest.length := by simp only [List.length_cons] at hj; omega
          have hfuel' : n ≥ rest.length + (N - y.toNat) := by
            simp only [List.length_cons] at hfuel; omega
          have hchain' : rest.IsChain (· ≤ ·) := hchain.tail
          have hbounds' : ∀ h' ∈ rest, y ≤ (h'.val : ℤ) + 1 := by
            intro h' hmem
            have hrel : h ≤ h' := hchain.rel_cons hmem
            have hh_bound : y ≤ (h.val : ℤ) + 1 := hbounds h List.mem_cons_self
            have h_ge : ¬ y < (h.val : ℤ) + 1 := hy_lt
            have hy_eq : y = (h.val : ℤ) + 1 := by omega
            have hval : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
            omega
          have hx_eq' : (buildVerticesAux N (x + 1) y rest n)[idx'].1 = (x + 1) + ↑(j - 1) := by
            have h1 : (x : ℤ) + j = (x + 1) + ((j : ℤ) - 1) := by ring
            have h2 : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
            rw [h2, ← h1, ← hx_eq]
          have ih_result := ih (x + 1) y rest hfuel' hy hyN hchain' hbounds' idx' hidx' (j - 1) hj' hx_eq'
          have hval_eq : (rest[j - 1] : Fin N).val = ((h :: rest)[j]'hj : Fin N).val := by
            cases j with
            | zero => omega
            | succ k => simp only [List.getElem_cons_succ, Nat.succ_sub_one]
          calc (buildVerticesAux N (x + 1) y rest n)[idx'].2
              ≤ ↑↑rest[j - 1] + 1 := ih_result
            _ = ↑((h :: rest)[j]'hj : Fin N).val + 1 := by rw [hval_eq]

/-- All y-coordinates in buildVerticesAux are ≥ the starting y-coordinate.
    This is because we only move north (y + 1) or east (same y), never south. -/
lemma buildVerticesAux_y_ge (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (idx : ℕ) (hidx : idx < (buildVerticesAux N x y heights fuel).length) :
    (buildVerticesAux N x y heights fuel)[idx].2 ≥ y := by
  induction fuel generalizing x y heights idx with
  | zero =>
    simp only [buildVerticesAux, List.length_singleton] at hidx
    have : idx = 0 := by omega
    subst this
    simp only [buildVerticesAux, List.getElem_singleton, ge_iff_le, le_refl]
  | succ n ih =>
    cases heights with
    | nil =>
      simp only [buildVerticesAux] at hidx ⊢
      split_ifs at hidx ⊢ with hy_lt
      · cases idx with
        | zero =>
          simp only [List.getElem_cons_zero, ge_iff_le, le_refl]
        | succ idx' =>
          have hidx' : idx' < (buildVerticesAux N x (y + 1) [] n).length := by
            simp only [List.length_cons] at hidx; omega
          have hih := ih x (y + 1) [] idx' hidx'
          simp only [ge_iff_le, List.getElem_cons_succ] at hih ⊢
          omega
      · simp only [List.length_singleton] at hidx
        have : idx = 0 := by omega
        subst this
        simp only [List.getElem_singleton, ge_iff_le, le_refl]
    | cons h rest =>
      simp only [buildVerticesAux] at hidx ⊢
      split_ifs at hidx ⊢ with hy_lt
      · cases idx with
        | zero =>
          simp only [List.getElem_cons_zero, ge_iff_le, le_refl]
        | succ idx' =>
          have hidx' : idx' < (buildVerticesAux N x (y + 1) (h :: rest) n).length := by
            simp only [List.length_cons] at hidx; omega
          have hih := ih x (y + 1) (h :: rest) idx' hidx'
          simp only [ge_iff_le, List.getElem_cons_succ] at hih ⊢
          omega
      · cases idx with
        | zero =>
          simp only [List.getElem_cons_zero, ge_iff_le, le_refl]
        | succ idx' =>
          have hidx' : idx' < (buildVerticesAux N (x + 1) y rest n).length := by
            simp only [List.length_cons] at hidx; omega
          have hge := ih (x + 1) y rest idx' hidx'
          simp only [ge_iff_le, List.getElem_cons_succ] at hge ⊢
          exact hge

/-- Y-coordinate lower bound invariant for buildVerticesAux.
    At x-coordinate x + j (after j east steps) where j > 0, the y-coordinate is at least heights[j-1].val + 1.
    This is because the (j-1)-th east step happened at y = heights[j-1].val + 1, and we never go south. -/
lemma buildVerticesAux_y_lower_bound (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (hfuel : fuel ≥ heights.length + (N - y.toNat)) (hy : 1 ≤ y) (hyN : y ≤ N)
    (hchain : heights.IsChain (· ≤ ·))
    (hbounds : ∀ h ∈ heights, y ≤ (h.val : ℤ) + 1)
    (idx : ℕ) (hidx : idx < (buildVerticesAux N x y heights fuel).length)
    (j : ℕ) (hj : j < heights.length) (hj_pos : 0 < j)
    (hx_eq : (buildVerticesAux N x y heights fuel)[idx].1 = x + j) :
    (buildVerticesAux N x y heights fuel)[idx].2 ≥ (heights[j - 1]).val + 1 := by
  induction fuel generalizing x y heights idx j with
  | zero =>
    simp only [buildVerticesAux, List.length_singleton] at hidx
    have hidx_eq : idx = 0 := by omega
    subst hidx_eq
    simp only [buildVerticesAux, List.getElem_singleton] at hx_eq
    -- At fuel = 0, x_coord = x, so j = 0, but hj_pos says j > 0, contradiction
    omega
  | succ n ih =>
    cases heights with
    | nil => simp at hj
    | cons h rest =>
      simp only [buildVerticesAux] at hidx hx_eq ⊢
      split_ifs at hidx hx_eq ⊢ with hy_lt
      · -- North case: y < h.val + 1
        cases idx with
        | zero =>
          simp only [List.getElem_cons_zero] at hx_eq
          -- At idx = 0, x_coord = x, so j = 0, but hj_pos says j > 0, contradiction
          omega
        | succ idx' =>
          simp only [List.length_cons] at hidx
          have hidx' : idx' < (buildVerticesAux N x (y + 1) (h :: rest) n).length := by omega
          simp only [List.getElem_cons_succ] at hx_eq ⊢
          have hfuel' : n ≥ (h :: rest).length + (N - (y + 1).toNat) := by
            simp only [List.length_cons] at hfuel ⊢
            have hy_pos : 0 ≤ y := by omega
            have h1 : (y + 1).toNat = y.toNat + 1 := by omega
            rw [h1]
            have hle : y.toNat < N := by
              have hh := h.isLt
              have hthis : y < N := by omega
              have htonat : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy_pos
              omega
            omega
          have hbounds' : ∀ h' ∈ (h :: rest), (y + 1) ≤ (h'.val : ℤ) + 1 := by
            intro h' hmem
            cases List.mem_cons.mp hmem with
            | inl heq => subst heq; omega
            | inr hrest =>
              have hrel : h ≤ h' := hchain.rel_cons hrest
              have hval : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
              omega
          have hyN' : y + 1 ≤ N := by
            have hh := h.isLt
            have hb := hbounds h List.mem_cons_self
            omega
          exact ih x (y + 1) (h :: rest) hfuel' (by omega) hyN' hchain hbounds' idx' hidx' j hj hj_pos hx_eq
      · -- East case: y ≥ h.val + 1, so y = h.val + 1 exactly (since y ≤ h.val + 1 from hbounds)
        have hy_eq : y = (h.val : ℤ) + 1 := by
          have hb := hbounds h List.mem_cons_self
          omega
        cases idx with
        | zero =>
          simp only [List.getElem_cons_zero] at hx_eq
          -- At idx = 0, x_coord = x, so j = 0, but hj_pos says j > 0, contradiction
          omega
        | succ idx' =>
          simp only [List.length_cons] at hidx
          have hidx' : idx' < (buildVerticesAux N (x + 1) y rest n).length := by omega
          simp only [List.getElem_cons_succ] at hx_eq ⊢
          have hx_ge := buildVerticesAux_x_ge N (x + 1) y rest n idx' hidx'
          -- After the east step, we're at x+1 with rest heights
          -- If j = 1, we need y ≥ heights[0].val + 1 = h.val + 1, which is true since y = h.val + 1
          -- If j > 1, we use IH with j-1
          cases j with
          | zero => omega  -- contradicts hj_pos
          | succ j' =>
            cases j' with
            | zero =>
              -- j = 1, need y ≥ heights[0].val + 1 = h.val + 1
              simp only [Nat.sub_self, List.getElem_cons_zero, ge_iff_le]
              -- The y-coordinate at idx' in the recursive call is ≥ y (since we never go south)
              have hy_lower := buildVerticesAux_y_ge N (x + 1) y rest n idx' hidx'
              calc (h.val : ℤ) + 1 = y := by omega
                _ ≤ (buildVerticesAux N (x + 1) y rest n)[idx'].2 := hy_lower
            | succ j'' =>
              -- j = j'' + 2 > 1, use IH with j - 1 = j'' + 1
              have hj' : j'' + 1 < rest.length := by simp only [List.length_cons] at hj; omega
              have hj'_pos : 0 < j'' + 1 := by omega
              have hfuel' : n ≥ rest.length + (N - y.toNat) := by
                simp only [List.length_cons] at hfuel; omega
              have hchain' : rest.IsChain (· ≤ ·) := hchain.tail
              have hbounds' : ∀ h' ∈ rest, y ≤ (h'.val : ℤ) + 1 := by
                intro h' hmem
                have hrel : h ≤ h' := hchain.rel_cons hmem
                have hval : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
                omega
              have hx_eq' : (buildVerticesAux N (x + 1) y rest n)[idx'].1 = (x + 1) + ↑(j'' + 1) := by
                have h1 : (x : ℤ) + (j'' + 2) = (x + 1) + (j'' + 1) := by ring
                have h2 : (j'' + 1 + 1 : ℕ) = j'' + 2 := by ring
                have h3 : ((j'' + 1 + 1 : ℕ) : ℤ) = ((j'' + 2 : ℕ) : ℤ) := by omega
                have h4 : ((j'' + 1 : ℕ) : ℤ) = (j'' : ℤ) + 1 := by omega
                omega
              have ih_result := ih (x + 1) y rest hfuel' hy hyN hchain' hbounds' idx' hidx' (j'' + 1) hj' hj'_pos hx_eq'
              -- ih_result says y_coord ≥ rest[j'' + 1 - 1].val + 1 = rest[j''].val + 1
              -- We need y_coord ≥ (h :: rest)[j'' + 2 - 1].val + 1 = (h :: rest)[j'' + 1].val + 1 = rest[j''].val + 1
              simp only [Nat.succ_sub_one, List.getElem_cons_succ]
              exact ih_result

/-- Consecutive vertices in buildVerticesAux satisfy the arc relation.
    Each step is either north (y+1) or east (x+1).
    
    **Proof sketch** (by induction on fuel):
    - Base case (fuel = 0): list is [(x, y)], length 1, no arcs to check (vacuously true)
    - Inductive case: split on heights (nil vs cons h rest)
      - For nil: split on y < N
        - If y < N: first vertex is (x, y), second is head of buildVerticesAux N x (y+1) [] n = (x, y+1)
          This is a north arc. Then apply IH for remaining arcs.
        - If y ≥ N: list is [(x, y)], length 1, no arcs
      - For cons h rest: split on y < h.val + 1
        - If y < h.val + 1: first arc is (x, y) → (x, y+1) (north), then apply IH
        - If y ≥ h.val + 1: first arc is (x, y) → (x+1, y) (east), then apply IH
    
    **Key technical issue**: The if-then-else in the goal must be simplified using the
    hypothesis (e.g., `simp only [hlt, ↓reduceIte]`), but this interacts poorly with
    List.get indexing. May need explicit `convert` or rewrites. -/
lemma buildVerticesAux_arcs_valid (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (hfuel : fuel ≥ heights.length + (N - y.toNat)) (hy : 1 ≤ y) (hyN : y ≤ N) :
    ∀ i : ℕ, ∀ hi : i + 1 < (buildVerticesAux N x y heights fuel).length,
      LGV.integerLattice.arc
        ((buildVerticesAux N x y heights fuel).get ⟨i, Nat.lt_of_succ_lt hi⟩)
        ((buildVerticesAux N x y heights fuel).get ⟨i + 1, hi⟩) := by
  induction fuel generalizing x y heights with
  | zero =>
    intro i hi
    simp only [buildVerticesAux, List.length_singleton] at hi
    omega
  | succ n ih =>
    intro i hi
    simp only [buildVerticesAux] at hi ⊢
    cases heights with
    | nil =>
      by_cases hy_lt : y < (N : ℤ)
      · -- y < N: list is (x, y) :: buildVerticesAux N x (y + 1) [] n
        simp only [List.get_eq_getElem, hy_lt, ↓reduceIte] at hi ⊢
        cases i with
        | zero =>
          -- Arc from (x, y) to (x, y + 1)
          have hne : buildVerticesAux N x (y + 1) [] n ≠ [] := buildVerticesAux_nonempty N x (y + 1) [] n
          have h1 : (buildVerticesAux N x (y + 1) [] n).head hne = (x, y + 1) := by
            apply buildVerticesAux_head; right; rfl
          simp only [List.getElem_cons_zero, List.getElem_cons_succ,
            List.head_eq_getElem_zero hne] at h1 ⊢
          rw [h1]
          rw [LGV.integerLattice_arc_iff]
          right; rfl
        | succ j =>
          simp only [List.getElem_cons_succ]
          have hi' : j + 1 < (buildVerticesAux N x (y + 1) [] n).length := by
            simp only [List.length_cons] at hi; omega
          have hfuel' : n ≥ ([] : List (Fin N)).length + (N - (y + 1).toNat) := by
            simp only [List.length_nil, zero_add]
            have hy_pos : 0 ≤ y := by omega
            have h1 : (y + 1).toNat = y.toNat + 1 := by
              have := Int.toNat_of_nonneg hy_pos; omega
            rw [h1]
            simp only [List.length_nil, zero_add] at hfuel
            omega
          have result := ih x (y + 1) [] hfuel' (by omega) (by omega) j hi'
          simp only [List.get_eq_getElem] at result
          exact result
      · -- y ≥ N: list is [(x, y)]
        simp only [hy_lt, ↓reduceIte, List.length_singleton] at hi
        omega
    | cons h rest =>
      by_cases hy_lt : y < (h.val : ℤ) + 1
      · -- y < h.val + 1: list is (x, y) :: buildVerticesAux N x (y + 1) (h :: rest) n
        simp only [List.get_eq_getElem, hy_lt, ↓reduceIte] at hi ⊢
        cases i with
        | zero =>
          have hne : buildVerticesAux N x (y + 1) (h :: rest) n ≠ [] :=
            buildVerticesAux_nonempty N x (y + 1) (h :: rest) n
          have h1 : (buildVerticesAux N x (y + 1) (h :: rest) n).head hne = (x, y + 1) := by
            apply buildVerticesAux_head
            left
            simp only [List.length_cons] at hfuel
            have hy_pos : 0 ≤ y := by omega
            have hN_y : N - y.toNat ≥ 1 := by
              have hh := h.isLt
              have h1 : y ≤ h.val := by omega
              have h2 : y.toNat = y := Int.toNat_of_nonneg hy_pos
              omega
            omega
          simp only [List.getElem_cons_zero, List.getElem_cons_succ,
            List.head_eq_getElem_zero hne] at h1 ⊢
          rw [h1]
          rw [LGV.integerLattice_arc_iff]
          right; rfl
        | succ j =>
          simp only [List.getElem_cons_succ]
          have hi' : j + 1 < (buildVerticesAux N x (y + 1) (h :: rest) n).length := by
            simp only [List.length_cons] at hi; omega
          have hfuel' : n ≥ (h :: rest).length + (N - (y + 1).toNat) := by
            simp only [List.length_cons]
            have hy_pos : 0 ≤ y := by omega
            have h1 : (y + 1).toNat = y.toNat + 1 := by
              have := Int.toNat_of_nonneg hy_pos; omega
            rw [h1]
            simp only [List.length_cons] at hfuel
            omega
          have hyN' : y + 1 ≤ N := by have hh := h.isLt; omega
          have result := ih x (y + 1) (h :: rest) hfuel' (by omega) hyN' j hi'
          simp only [List.get_eq_getElem] at result
          exact result
      · -- y ≥ h.val + 1: list is (x, y) :: buildVerticesAux N (x + 1) y rest n
        simp only [List.get_eq_getElem, hy_lt, ↓reduceIte] at hi ⊢
        cases i with
        | zero =>
          have hne : buildVerticesAux N (x + 1) y rest n ≠ [] :=
            buildVerticesAux_nonempty N (x + 1) y rest n
          have h1 : (buildVerticesAux N (x + 1) y rest n).head hne = (x + 1, y) := by
            apply buildVerticesAux_head
            cases rest with
            | nil => right; rfl
            | cons _ _ =>
              left
              simp only [List.length_cons] at hfuel
              omega
          simp only [List.getElem_cons_zero, List.getElem_cons_succ,
            List.head_eq_getElem_zero hne] at h1 ⊢
          rw [h1]
          rw [LGV.integerLattice_arc_iff]
          left; rfl
        | succ j =>
          simp only [List.getElem_cons_succ]
          have hi' : j + 1 < (buildVerticesAux N (x + 1) y rest n).length := by
            simp only [List.length_cons] at hi; omega
          have hfuel' : n ≥ rest.length + (N - y.toNat) := by
            simp only [List.length_cons] at hfuel; omega
          have result := ih (x + 1) y rest hfuel' hy hyN j hi'
          simp only [List.get_eq_getElem] at result
          exact result

/-- Helper: toNat of (y + 1) equals toNat of y plus 1 when y is nonnegative. -/
lemma toNat_add_one_of_nonneg (y : ℤ) (hy_pos : 0 ≤ y) : (y + 1).toNat = y.toNat + 1 := by
  have h1 : (y + 1) = (y.toNat : ℤ) + 1 := by rw [Int.toNat_of_nonneg hy_pos]
  conv_lhs => rw [h1]
  simp only [Int.toNat_natCast_add_one]

/-- The last vertex built by buildVerticesAux is (x + heights.length, N) when fuel is sufficient.
    
    **Proof sketch** (by induction on fuel with generalized x, y, heights):
    - Base case (fuel = 0): list is [(x, y)], so getLast = (x, y).
      Need to show (x, y) = (x + heights.length, N).
      From hfuel: 0 ≥ heights.length + (N - y.toNat), so heights = [] and y = N.
      Then x + [].length = x and we're done.
    - Inductive case: split on heights (nil vs cons)
      - For nil: split on y < N
        - If y < N: getLast of (x,y) :: buildVerticesAux N x (y+1) [] n
          = getLast of buildVerticesAux N x (y+1) [] n (since list is nonempty)
          By IH, this is (x + [].length, N) = (x, N) = (x + 0, N). ✓
        - If y ≥ N: list is [(x, y)], so getLast = (x, y) = (x + 0, N) since y = N. ✓
      - For cons h rest: split on y < h.val + 1
        - If y < h.val + 1: getLast = getLast of buildVerticesAux N x (y+1) (h::rest) n
          By IH with same heights, this is (x + (h::rest).length, N). ✓
        - If y ≥ h.val + 1: getLast = getLast of buildVerticesAux N (x+1) y rest n
          By IH with rest, this is ((x+1) + rest.length, N) = (x + (h::rest).length, N). ✓
    
    **Key**: The hchain and hbounds hypotheses ensure the algorithm processes heights
    in order and doesn't skip any. -/
lemma buildVerticesAux_getLast (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (hfuel : fuel ≥ heights.length + (N - y.toNat)) (hy : 1 ≤ y) (hyN : y ≤ N)
    (_hN : 0 < N)
    (hchain : heights.IsChain (· ≤ ·))
    (hbounds : ∀ h ∈ heights, y ≤ (h.val : ℤ) + 1) :
    (buildVerticesAux N x y heights fuel).getLast (buildVerticesAux_nonempty N x y heights fuel) =
    (x + heights.length, (N : ℤ)) := by
  induction fuel generalizing x y heights with
  | zero =>
    simp only [buildVerticesAux, List.getLast_singleton]
    have hlen : heights.length = 0 := by omega
    have h2 : N ≤ y.toNat := by omega
    have hynonneg : 0 ≤ y := by omega
    have hyN' : y.toNat ≤ N := by
      have := Int.toNat_of_nonneg hynonneg
      omega
    have htonat_eq : y.toNat = N := le_antisymm hyN' h2
    have hy_eq : y = N := by
      have := Int.toNat_of_nonneg hynonneg
      omega
    rw [hlen, hy_eq]
    ring_nf
  | succ n ih =>
    cases heights with
    | nil =>
      simp only [List.length_nil]
      simp only [buildVerticesAux]
      split_ifs with hy_lt
      · -- y < N, so we recurse north
        simp only [List.getLast_cons (buildVerticesAux_nonempty N x (y + 1) [] n)]
        have hfuel' : n ≥ ([] : List (Fin N)).length + (N - (y + 1).toNat) := by
          simp only [List.length_nil, zero_add]
          have hy_pos : 0 ≤ y := by omega
          have h1 : (y + 1).toNat = y.toNat + 1 := toNat_add_one_of_nonneg y hy_pos
          rw [h1]
          simp only [List.length_nil, zero_add] at hfuel
          omega
        have ih_result := ih x (y + 1) ([] : List (Fin N)) hfuel' (by omega) (by omega)
          List.isChain_nil (by simp)
        simp only [List.length_nil, Nat.cast_zero, add_zero] at ih_result ⊢
        exact ih_result
      · -- y ≥ N, so y = N
        simp only [List.getLast_singleton]
        have : y = N := by
          have h1 : y ≤ N := hyN
          have h2 : ¬ y < N := hy_lt
          omega
        simp [this]
    | cons h rest =>
      simp only [buildVerticesAux]
      split_ifs with hy_lt
      · -- North case: y < h.val + 1
        simp only [List.getLast_cons (buildVerticesAux_nonempty N x (y + 1) (h :: rest) n)]
        have hy_pos : 0 ≤ y := by omega
        have h1 : (y + 1).toNat = y.toNat + 1 := toNat_add_one_of_nonneg y hy_pos
        have hfuel' : n ≥ (h :: rest).length + (N - (y + 1).toNat) := by
          simp only [List.length_cons] at hfuel ⊢
          rw [h1]
          have hle : y.toNat < N := by
            have hh := h.isLt
            have : y < N := by omega
            have htonat : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy_pos
            omega
          omega
        have hbounds' : ∀ h' ∈ (h :: rest), (y + 1) ≤ (h'.val : ℤ) + 1 := by
          intro h' hmem
          cases List.mem_cons.mp hmem with
          | inl heq =>
            subst heq
            omega
          | inr hrest =>
            have hrel : h ≤ h' := hchain.rel_cons hrest
            have : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
            omega
        have hyN' : y + 1 ≤ N := by
          have hh := h.isLt
          have hb := hbounds h List.mem_cons_self
          omega
        have ih_result := ih x (y + 1) (h :: rest) hfuel' (by omega) hyN' hchain hbounds'
        exact ih_result
      · -- East case: y ≥ h.val + 1
        simp only [List.getLast_cons (buildVerticesAux_nonempty N (x + 1) y rest n)]
        have hfuel' : n ≥ rest.length + (N - y.toNat) := by
          simp only [List.length_cons] at hfuel
          omega
        have hchain' : rest.IsChain (· ≤ ·) := hchain.tail
        have hbounds' : ∀ h' ∈ rest, y ≤ (h'.val : ℤ) + 1 := by
          intro h' hmem
          have hrel : h ≤ h' := hchain.rel_cons hmem
          have hh_bound : y ≤ (h.val : ℤ) + 1 := hbounds h List.mem_cons_self
          have h_ge : ¬ y < (h.val : ℤ) + 1 := hy_lt
          have hy_eq : y = (h.val : ℤ) + 1 := by omega
          have : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
          omega
        have ih_result := ih (x + 1) y rest hfuel' hy hyN hchain' hbounds'
        simp only [List.length_cons]
        convert ih_result using 1
        push_cast
        ring_nf

/-- Wrapper: buildVertices produces valid arcs. -/
lemma buildVertices_arcs_valid (a c : ℤ) (N : ℕ) (eastStepHeights : List (Fin N))
    (_hN : 0 < N) (hlen : eastStepHeights.length = (c - a).toNat) (_h : 0 ≤ c - a) :
    ∀ i : ℕ, ∀ hi : i + 1 < (buildVertices a c N eastStepHeights).length,
      LGV.integerLattice.arc
        ((buildVertices a c N eastStepHeights).get ⟨i, Nat.lt_of_succ_lt hi⟩)
        ((buildVertices a c N eastStepHeights).get ⟨i + 1, hi⟩) := by
  simp only [buildVertices]
  apply buildVerticesAux_arcs_valid
  · simp only [hlen]; omega
  · omega
  · omega

/-- Wrapper: buildVertices ends at (c, N). -/
lemma buildVertices_getLast (a c : ℤ) (N : ℕ) (eastStepHeights : List (Fin N))
    (hN : 0 < N) (hlen : eastStepHeights.length = (c - a).toNat) (h : 0 ≤ c - a)
    (hchain : eastStepHeights.IsChain (· ≤ ·)) :
    (buildVertices a c N eastStepHeights).getLast (buildVertices_nonempty a c N eastStepHeights) =
    (c, (N : ℤ)) := by
  simp only [buildVertices]
  have hbounds : ∀ h ∈ eastStepHeights, (1 : ℤ) ≤ (h.val : ℤ) + 1 := by
    intro h _; omega
  have hfuel : (c - a).toNat + N ≥ eastStepHeights.length + (N - (1 : ℤ).toNat) := by
    simp only [hlen, Int.toNat_one]; omega
  have hlast := buildVerticesAux_getLast N a 1 eastStepHeights ((c - a).toNat + N)
    hfuel (by omega) (by omega) hN hchain hbounds
  simp only [hlen] at hlast
  -- hlast says the last vertex is (a + (c-a).toNat, N)
  -- We need to show this equals (c, N)
  -- Since 0 ≤ c - a, we have (c - a).toNat = c - a (as integers)
  -- So a + (c - a).toNat = a + (c - a) = c
  rw [hlast]
  congr 1
  have hca : (c - a).toNat = c - a := Int.toNat_of_nonneg h
  omega


/-- Y-coordinate upper bound at x = a + k: the y-coordinate is at most heights[k].val + 1.

    This captures the key property that at x-coordinate a + k (after k east steps),
    the path has not yet passed the k-th east step height. The east step at position k
    happens at y = heights[k].val + 1, so any vertex at x = a + k has y ≤ heights[k].val + 1.

    This is used in the surjectivity proof to show that paths with column-strict heights
    cannot share vertices. -/
lemma buildVertices_y_upper_bound_at_x (a c : ℤ) (N : ℕ) (heights : List (Fin N))
    (_hN : 0 < N) (hlen : heights.length = (c - a).toNat) (_h : 0 ≤ c - a)
    (hchain : heights.IsChain (· ≤ ·))
    (idx : ℕ) (hidx : idx < (buildVertices a c N heights).length)
    (k : ℕ) (hk : k < heights.length)
    (hx_eq : (buildVertices a c N heights)[idx].1 = a + k) :
    (buildVertices a c N heights)[idx].2 ≤ (heights[k]).val + 1 := by
  simp only [buildVertices] at hidx hx_eq ⊢
  have hfuel : (c - a).toNat + N ≥ heights.length + (N - (1 : ℤ).toNat) := by
    simp only [hlen, Int.toNat_one]; omega
  have hbounds : ∀ h ∈ heights, (1 : ℤ) ≤ (h.val : ℤ) + 1 := by
    intro h _; omega
  exact buildVerticesAux_y_upper_bound N a 1 heights ((c - a).toNat + N)
    hfuel (by omega) (by omega) hchain hbounds idx hidx k hk hx_eq


/-- Y-coordinate lower bound at x = a + k for k > 0: the y-coordinate is at least heights[k-1].val + 1.

    This captures the key property that at x-coordinate a + k (after k east steps),
    the path has already passed the (k-1)-th east step height. The east step at position k-1
    happens at y = heights[k-1].val + 1, so any vertex at x = a + k has y ≥ heights[k-1].val + 1.

    This is used in the surjectivity proof to show that paths with column-strict heights
    cannot share vertices. -/
lemma buildVertices_y_lower_bound_at_x (a c : ℤ) (N : ℕ) (heights : List (Fin N))
    (_hN : 0 < N) (hlen : heights.length = (c - a).toNat) (_h : 0 ≤ c - a)
    (hchain : heights.IsChain (· ≤ ·))
    (idx : ℕ) (hidx : idx < (buildVertices a c N heights).length)
    (k : ℕ) (hk : k < heights.length) (hk_pos : 0 < k)
    (hx_eq : (buildVertices a c N heights)[idx].1 = a + k) :
    (buildVertices a c N heights)[idx].2 ≥ (heights[k - 1]).val + 1 := by
  simp only [buildVertices] at hidx hx_eq ⊢
  have hfuel : (c - a).toNat + N ≥ heights.length + (N - (1 : ℤ).toNat) := by
    simp only [hlen, Int.toNat_one]; omega
  have hbounds : ∀ h ∈ heights, (1 : ℤ) ≤ (h.val : ℤ) + 1 := by
    intro h _; omega
  exact buildVerticesAux_y_lower_bound N a 1 heights ((c - a).toNat + N)
    hfuel (by omega) (by omega) hchain hbounds idx hidx k hk hk_pos hx_eq

/-- Y-coordinate lower bound at x = a + heights.length (last column): y ≥ heights[last] + 1.

    At the last column (after all east steps), the y-coordinate is at least the last
    east-step height plus 1. This is because the last east step happens at y = heights[last] + 1,
    and after that we only go north.

    This complements `buildVertices_y_lower_bound_at_x` which handles k < heights.length. -/
lemma buildVertices_y_lower_bound_at_last_column (a c : ℤ) (N : ℕ) (heights : List (Fin N))
    (hN : 0 < N) (hlen : heights.length = (c - a).toNat) (_h : 0 ≤ c - a)
    (hchain : heights.IsChain (· ≤ ·))
    (hlen_pos : 0 < heights.length)
    (idx : ℕ) (hidx : idx < (buildVertices a c N heights).length)
    (hx_eq : (buildVertices a c N heights)[idx].1 = a + heights.length) :
    (buildVertices a c N heights)[idx].2 ≥ (heights[heights.length - 1]).val + 1 := by
  -- At x = a + heights.length, all east steps have been consumed.
  -- The y-coordinate is at least heights[last] + 1.
  -- This follows from buildVertices_y_lower_bound_at_x with k = heights.length - 1 + 1 = heights.length
  -- But that lemma requires k < heights.length, so we need a different approach.
  --
  -- Alternative: use the fact that at the last column, we've made heights.length east steps,
  -- so we're at or past the last east-step height.
  --
  -- The proof uses buildVertices_y_lower_bound_at_x for k = heights.length - 1 < heights.length,
  -- noting that at x = a + heights.length, we must have passed through x = a + (heights.length - 1) + 1.
  -- At that point, y ≥ heights[heights.length - 2] + 1 (if heights.length > 1).
  -- But we need y ≥ heights[heights.length - 1] + 1.
  --
  -- Actually, the key is that at x = a + k, the y-coordinate is at least heights[k-1] + 1.
  -- At x = a + heights.length = a + (heights.length - 1) + 1, this gives y ≥ heights[heights.length - 2] + 1.
  -- But we need heights[heights.length - 1] + 1.
  --
  -- The correct approach: after the last east step (at x = a + heights.length - 1 → a + heights.length),
  -- the y-coordinate is exactly heights[heights.length - 1] + 1. After that, we only go north,
  -- so any vertex at x = a + heights.length has y ≥ heights[heights.length - 1] + 1.
  --
  -- We prove this by induction on the buildVerticesAux structure.
  simp only [buildVertices] at hidx hx_eq ⊢
  -- We need to show that at x = a + heights.length, y ≥ heights[last] + 1
  -- This follows from the structure of buildVerticesAux: when heights is empty,
  -- we only go north, so y is preserved or increased.
  -- The last east step sets y = heights[last] + 1, so after that y ≥ heights[last] + 1.
  have hfuel : (c - a).toNat + N ≥ heights.length + (N - (1 : ℤ).toNat) := by
    simp only [hlen, Int.toNat_one]; omega
  -- Use the fact that at x = a + heights.length, all heights have been consumed
  -- and y ≥ heights[last] + 1 from the last east step
  have key : ∀ (x y : ℤ) (heights' : List (Fin N)) (fuel : ℕ)
      (hfuel' : fuel ≥ heights'.length + (N - y.toNat))
      (hy : 1 ≤ y) (hyN : y ≤ N)
      (hchain' : heights'.IsChain (· ≤ ·))
      (hbounds : ∀ h' ∈ heights', y ≤ (h'.val : ℤ) + 1)
      (idx' : ℕ) (hidx' : idx' < (buildVerticesAux N x y heights' fuel).length)
      (hx_eq' : (buildVerticesAux N x y heights' fuel)[idx'].1 = x + heights'.length)
      (hlen_pos' : heights'.length > 0),
      (buildVerticesAux N x y heights' fuel)[idx'].2 ≥ (heights'[heights'.length - 1]'(by omega)).val + 1 := by
    intro x' y' heights' fuel hfuel' hy hyN hchain' hbounds idx' hidx' hx_eq' hlen_pos'
    induction fuel generalizing x' y' heights' idx' with
    | zero =>
      simp only [buildVerticesAux, List.length_singleton] at hidx'
      have hidx_eq : idx' = 0 := by omega
      subst hidx_eq
      simp only [buildVerticesAux, List.getElem_singleton] at hx_eq'
      -- x' = x' + heights'.length implies heights'.length = 0, contradicting hlen_pos'
      omega
    | succ n ih =>
      cases heights' with
      | nil => simp at hlen_pos'
      | cons h rest =>
        simp only [buildVerticesAux] at hidx' hx_eq' ⊢
        split_ifs at hidx' hx_eq' ⊢ with hy_lt
        · -- North case: y' < h.val + 1
          cases idx' with
          | zero =>
            simp only [List.getElem_cons_zero] at hx_eq'
            -- x' = x' + (h :: rest).length implies (h :: rest).length = 0, contradiction
            simp only [List.length_cons] at hx_eq'
            omega
          | succ idx'' =>
            simp only [List.length_cons] at hidx'
            have hidx'' : idx'' < (buildVerticesAux N x' (y' + 1) (h :: rest) n).length := by omega
            simp only [List.getElem_cons_succ] at hx_eq' ⊢
            have hfuel'' : n ≥ (h :: rest).length + (N - (y' + 1).toNat) := by
              simp only [List.length_cons] at hfuel' ⊢
              have hy_pos : 0 ≤ y' := by omega
              have h1 : (y' + 1).toNat = y'.toNat + 1 := by omega
              rw [h1]
              have hle : y'.toNat < N := by
                have hh := h.isLt
                have hthis : y' < N := by omega
                have htonat : (y'.toNat : ℤ) = y' := Int.toNat_of_nonneg hy_pos
                omega
              omega
            have hbounds' : ∀ h' ∈ (h :: rest), (y' + 1) ≤ (h'.val : ℤ) + 1 := by
              intro h' hmem
              cases List.mem_cons.mp hmem with
              | inl heq => subst heq; omega
              | inr hrest =>
                have hrel : h ≤ h' := hchain'.rel_cons hrest
                have hval : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
                omega
            have hyN' : y' + 1 ≤ N := by
              have hh := h.isLt
              have hb := hbounds h List.mem_cons_self
              omega
            exact ih x' (y' + 1) (h :: rest) hfuel'' (by omega) hyN' hchain' hbounds' idx'' hidx'' hx_eq'
              (by simp only [List.length_cons]; omega)
        · -- East case: y' ≥ h.val + 1
          have hy_eq : y' = (h.val : ℤ) + 1 := by
            have hb := hbounds h List.mem_cons_self
            omega
          cases idx' with
          | zero =>
            simp only [List.getElem_cons_zero] at hx_eq'
            -- x' = x' + (h :: rest).length implies (h :: rest).length = 0, contradiction
            simp only [List.length_cons] at hx_eq'
            omega
          | succ idx'' =>
            simp only [List.length_cons] at hidx'
            have hidx'' : idx'' < (buildVerticesAux N (x' + 1) y' rest n).length := by omega
            simp only [List.getElem_cons_succ] at hx_eq' ⊢
            -- After east step, we're at x' + 1 with rest heights
            -- rest.length = (h :: rest).length - 1
            have hrest_len : rest.length = (h :: rest).length - 1 := by simp
            -- At x' + 1 + rest.length = x' + (h :: rest).length
            have hx_eq'' : (buildVerticesAux N (x' + 1) y' rest n)[idx''].1 = (x' + 1) + rest.length := by
              simp only [List.length_cons] at hx_eq'
              have h1 : (x' : ℤ) + (rest.length + 1) = (x' + 1) + rest.length := by ring
              omega
            cases rest with
            | nil =>
              -- rest is empty, so we're at the last column
              -- The y-coordinate is y' = h.val + 1 = heights[0].val + 1
              simp only [List.length_nil] at hx_eq''
              have hy_ge := buildVerticesAux_y_ge N (x' + 1) y' [] n idx'' hidx''
              simp only [List.length_cons, List.length_nil]
              calc (h.val : ℤ) + 1 = y' := by omega
                _ ≤ (buildVerticesAux N (x' + 1) y' [] n)[idx''].2 := hy_ge
            | cons h' rest' =>
              -- rest is non-empty, apply IH
              have hfuel'' : n ≥ (h' :: rest').length + (N - y'.toNat) := by
                simp only [List.length_cons] at hfuel' ⊢
                omega
              have hchain'' : (h' :: rest').IsChain (· ≤ ·) := hchain'.tail
              have hbounds'' : ∀ h'' ∈ (h' :: rest'), y' ≤ (h''.val : ℤ) + 1 := by
                intro h'' hmem
                -- h'' ∈ h' :: rest' means h'' ∈ rest (since rest = h' :: rest')
                -- hchain' is for h :: rest = h :: h' :: rest'
                -- We need h ≤ h'' which follows from hchain'.rel_cons
                have hmem' : h'' ∈ (h :: h' :: rest') := List.mem_cons_of_mem h hmem
                have hrel : h ≤ h'' := hchain'.rel_cons hmem
                have hval : (h.val : ℤ) ≤ h''.val := Int.ofNat_le.mpr hrel
                omega
              have ih_result := ih (x' + 1) y' (h' :: rest') hfuel'' (by omega) (by omega) hchain'' hbounds''
                idx'' hidx'' hx_eq'' (by simp only [List.length_cons]; omega)
              -- ih_result says y ≥ (h' :: rest')[last].val + 1
              -- We need y ≥ (h :: h' :: rest')[last].val + 1 = (h' :: rest')[last].val + 1
              simp only [List.length_cons, Nat.add_one_sub_one] at ih_result ⊢
              exact ih_result
  have hbounds : ∀ h' ∈ heights, (1 : ℤ) ≤ (h'.val : ℤ) + 1 := fun _ _ => by omega
  exact key a 1 heights ((c - a).toNat + N) hfuel (by omega) (by omega) hchain hbounds idx hidx hx_eq hlen_pos


/-- Helper: pathWeightAux with jacobiTrudiArcWeight equals the product over lgvPathEastStepYCoords.

    This is the key lemma relating the arc-based weight computation to the east-step height list.
    For each east-step at y-coordinate y (where 1 ≤ y ≤ N), the arc weight is X_{(y-1).toNat}.
    North-steps have weight 1 and don't contribute to the product.

    The proof proceeds by induction on the vertex list:
    - Base case: single vertex has weight 1 and no east-steps
    - Inductive case: for v₀ :: v₁ :: rest, the first arc is either:
      * East-step: contributes X_{v₀.2 - 1} to weight and v₀.2 to lgvPathEastStepYCoords
      * North-step: contributes 1 to weight and nothing to lgvPathEastStepYCoords

    The induction hypothesis applies to the tail (v₁ :: rest). -/
lemma pathWeightAux_eq_prod_eastStepYCoords (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (h_bounded : ∀ y ∈ lgvPathEastStepYCoords vertices, 1 ≤ y ∧ y ≤ N) :
    LGV.pathWeightAux (jacobiTrudiArcWeight (N := N) (R := R)) vertices h_arcs =
    ((lgvPathEastStepYCoords vertices).pmap
      (fun y hy => MvPolynomial.X (R := R)
        (⟨(y - 1).toNat, by have := h_bounded y hy; omega⟩ : Fin N))
      (fun _ hy => hy)).prod := by
  -- Proof by induction on the vertex list structure
  -- For each east-step at height y, jacobiTrudiArcWeight gives X_{y-1}
  -- For north-steps, the weight is 1
  -- lgvPathEastStepYCoords collects exactly the east-step heights
  induction vertices with
  | nil => exact absurd rfl h_ne
  | cons v₀ vs ih =>
    cases vs with
    | nil =>
      simp only [LGV.pathWeightAux, lgvPathEastStepYCoords, List.pmap, List.prod_nil]
    | cons v₁ rest =>
      have h_arc : LGV.integerLattice.arc v₀ v₁ := by
        have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
        simp at this
        exact this
      have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
          LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
            ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
        intro i hi
        have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
        have := h_arcs (i + 1) hi'
        simp at this ⊢
        exact this
      have h_ne' : v₁ :: rest ≠ [] := List.cons_ne_nil v₁ rest

      simp only [LGV.integerLattice] at h_arc
      rcases h_arc with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · -- East-step case: v₁.1 = v₀.1 + 1 ∧ v₁.2 = v₀.2
        simp only [lgvPathEastStepYCoords, hx, hy, and_self, ↓reduceIte]
        simp only [LGV.pathWeightAux]
        simp only [jacobiTrudiArcWeight, hx, hy, and_self, ↓reduceIte]

        have h_bounded' : ∀ y ∈ lgvPathEastStepYCoords (v₁ :: rest), 1 ≤ y ∧ y ≤ N := by
          intro y hy'
          apply h_bounded y
          simp only [lgvPathEastStepYCoords, hx, hy, and_self, ↓reduceIte]
          exact List.mem_cons_of_mem _ hy'

        have h_v0_bounded : 1 ≤ v₀.2 ∧ v₀.2 ≤ N := by
          apply h_bounded v₀.2
          simp only [lgvPathEastStepYCoords, hx, hy, and_self, ↓reduceIte]
          exact List.mem_cons_self

        simp only [h_v0_bounded]

        have ih' := ih h_ne' h_arcs' h_bounded'

        simp only [List.pmap, List.prod_cons]
        congr 1
        rw [ih']
        congr 1
        apply List.pmap_congr_left
        intro x hx hx' h₂
        rfl

      · -- North-step case: v₁.1 = v₀.1 ∧ v₁.2 = v₀.2 + 1
        have h_not_east : ¬(v₁.1 = v₀.1 + 1 ∧ v₁.2 = v₀.2) := by omega
        have heq : lgvPathEastStepYCoords (v₀ :: v₁ :: rest) = lgvPathEastStepYCoords (v₁ :: rest) := by
          simp only [lgvPathEastStepYCoords, h_not_east, ↓reduceIte]
        
        simp only [LGV.pathWeightAux, jacobiTrudiArcWeight, h_not_east, ↓reduceIte, one_mul]
        
        have h_bounded' : ∀ y ∈ lgvPathEastStepYCoords (v₁ :: rest), 1 ≤ y ∧ y ≤ N := by
          intro y hy'
          apply h_bounded y
          rw [heq]
          exact hy'

        have ih' := ih h_ne' h_arcs' h_bounded'
        rw [ih']
        congr 1
        simp only [heq]
        -- The two sides are definitionally equal, but have different proof terms
        -- Use proof irrelevance via List.pmap_congr_left
        apply List.pmap_congr_left
        intro x hx hx' h₂
        rfl

/-- Helper lemma: pathWeightAux with jacobiTrudiArcWeight equals the product over
    lgvPathEastStepYCoords converted to Fin N.

    This is the key lemma relating the arc-based weight computation to the east-step height list.
    For each east-step at y-coordinate y (where 1 ≤ y ≤ N), the arc weight is X_{(y-1).toNat}.
    North-steps have weight 1 and don't contribute to the product. -/
lemma pathWeightAux_eq_map_prod_lgvYCoords (vertices : List (ℤ × ℤ))
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (h_bounded : ∀ y ∈ lgvPathEastStepYCoords vertices, 1 ≤ y ∧ y ≤ N) :
    LGV.pathWeightAux (jacobiTrudiArcWeight (N := N) (R := R)) vertices h_arcs =
    (List.map (fun j => X j) (lgvYCoordsToFinN (lgvPathEastStepYCoords vertices) h_bounded)).prod := by
  induction vertices with
  | nil =>
    simp [LGV.pathWeightAux, lgvPathEastStepYCoords, lgvYCoordsToFinN]
  | cons v vs ih =>
    cases vs with
    | nil =>
      simp [LGV.pathWeightAux, lgvPathEastStepYCoords, lgvYCoordsToFinN]
    | cons v' rest =>
      simp only [LGV.pathWeightAux, lgvPathEastStepYCoords]
      have h_arc : LGV.integerLattice.arc v v' := by
        have := h_arcs 0 (by simp : 0 + 1 < (v :: v' :: rest).length)
        simp at this
        exact this
      rcases h_arc with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · -- East-step case: v'.1 = v.1 + 1, v'.2 = v.2
        have heast : v'.1 = v.1 + 1 ∧ v'.2 = v.2 := ⟨hx, hy⟩
        simp only [heast, and_self, ↓reduceIte]
        simp only [lgvYCoordsToFinN, List.pmap, List.map]
        rw [List.prod_cons]
        -- Prepare the induction hypothesis arguments
        have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v' :: rest).length,
            LGV.integerLattice.arc ((v' :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((v' :: rest).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v :: v' :: rest).length := by simp at hi ⊢; omega
          have := h_arcs (i + 1) hi'
          simp at this ⊢
          exact this
        have h_bounded' : ∀ y ∈ lgvPathEastStepYCoords (v' :: rest), 1 ≤ y ∧ y ≤ N := by
          intro y hy
          apply h_bounded y
          simp only [lgvPathEastStepYCoords, heast, and_self, ↓reduceIte, List.mem_cons]
          right
          exact hy
        -- Show the first factors are equal
        have hv2_bounded : 1 ≤ v.2 ∧ v.2 ≤ N := by
          apply h_bounded v.2
          simp [lgvPathEastStepYCoords, heast]
        have hfirst : jacobiTrudiArcWeight (N := N) (R := R) v v' (Or.inl heast) =
            X ⟨(v.2 - 1).toNat, by have := hv2_bounded; omega⟩ := by
          unfold jacobiTrudiArcWeight
          simp only [heast, and_self, ↓reduceIte, hv2_bounded, dif_pos]
        -- The goal is: jacobiTrudiArcWeight * pathWeightAux = X * (map X pmap).prod
        -- Use hfirst for the first factor
        rw [hfirst]
        -- Now goal is: X * pathWeightAux = X * (map X pmap).prod
        -- Show the second factors are equal using IH
        rw [ih h_arcs' h_bounded']
        -- Now goal is: X * (map X (lgvYCoordsToFinN ...)).prod = X * (map X pmap).prod
        -- The two pmap expressions differ only in proof arguments
        simp only [lgvYCoordsToFinN]
        -- The two sides differ in the proof argument to pmap, but produce the same Fin N values
        -- Use List.map_pmap to convert to a form where we can use congr
        rw [List.map_pmap, List.map_pmap]
        -- Now both sides are pmap of (fun y _ => X ⟨(y-1).toNat, _⟩)
        -- The function doesn't use the proof, so the results are equal
        -- The two pmaps have the same underlying list and produce the same values
        -- because the Fin N constructor only depends on (y-1).toNat, not on the proof
        -- Goal: X _ * (pmap f l h₁).prod = X _ * (pmap f l h₂).prod
        -- The first factors are equal (both are X ⟨(v.2 - 1).toNat, _⟩)
        -- The second factors are equal because the pmaps produce the same list
        apply congrArg₂ (· * ·) rfl
        apply congrArg List.prod
        apply List.ext_getElem (by simp [List.length_pmap])
        intro i h1 h2
        simp only [List.getElem_pmap]
      · -- North-step case: v'.1 = v.1, v'.2 = v.2 + 1
        have hnorth : ¬(v'.1 = v.1 + 1 ∧ v'.2 = v.2) := by omega
        simp only [hnorth, ↓reduceIte]
        -- For north-step, jacobiTrudiArcWeight = 1
        have hw1 : jacobiTrudiArcWeight (N := N) (R := R) v v' (Or.inr ⟨hx, hy⟩) = 1 := by
          unfold jacobiTrudiArcWeight
          simp only [hnorth, ↓reduceIte]
        rw [hw1, one_mul]
        -- Use IH
        have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v' :: rest).length,
            LGV.integerLattice.arc ((v' :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((v' :: rest).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v :: v' :: rest).length := by simp at hi ⊢; omega
          have := h_arcs (i + 1) hi'
          simp at this ⊢
          exact this
        have h_bounded' : ∀ y ∈ lgvPathEastStepYCoords (v' :: rest), 1 ≤ y ∧ y ≤ N := by
          intro y hy
          apply h_bounded y
          simp only [lgvPathEastStepYCoords, hnorth, ↓reduceIte]
          exact hy
        rw [ih h_arcs' h_bounded']

lemma lgvPathToLatticePath_weight_eq (a c : ℤ) (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (hstart : p.start = (a, 1)) (hfinish : p.finish = (c, (N : ℤ))) :
    LGV.pathWeight (jacobiTrudiArcWeight (N := N) (R := R)) p =
    (lgvPathToLatticePath a c p hstart hfinish).weight (R := R) := by
  unfold LGV.pathWeight lgvPathToLatticePath LatticePath.weight
  simp only
  -- Apply the helper lemma
  apply pathWeightAux_eq_map_prod_lgvYCoords

/-- Helper: buildVerticesAux always starts with (x, y). -/
lemma buildVerticesAux_head' (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ) :
    ∃ tail, buildVerticesAux N x y heights fuel = (x, y) :: tail := by
  cases fuel with
  | zero => exact ⟨[], rfl⟩
  | succ n =>
    cases heights with
    | nil =>
      simp only [buildVerticesAux]
      split_ifs with h
      · exact ⟨buildVerticesAux N x (y + 1) [] n, rfl⟩
      · exact ⟨[], rfl⟩
    | cons h rest =>
      simp only [buildVerticesAux]
      split_ifs with hlt
      · exact ⟨buildVerticesAux N x (y + 1) (h :: rest) n, rfl⟩
      · exact ⟨buildVerticesAux N (x + 1) y rest n, rfl⟩

/-- Helper for lgvPathEastStepYCoords when we know the next vertex is a north step. -/
lemma lgvPathEastStepYCoords_cons_north_gen (x y : ℤ) (tail : List (ℤ × ℤ))
    (hhead : ∃ tail', tail = (x, y + 1) :: tail') :
    lgvPathEastStepYCoords ((x, y) :: tail) = lgvPathEastStepYCoords tail := by
  obtain ⟨tail', heq⟩ := hhead
  subst heq
  simp only [lgvPathEastStepYCoords]
  have h : ¬(x = x + 1 ∧ y + 1 = y) := by omega
  simp only [h, ↓reduceIte]

/-- Helper for lgvPathEastStepYCoords when we know the next vertex is an east step. -/
lemma lgvPathEastStepYCoords_cons_east_gen (x y : ℤ) (tail : List (ℤ × ℤ))
    (hhead : ∃ tail', tail = (x + 1, y) :: tail') :
    lgvPathEastStepYCoords ((x, y) :: tail) = y :: lgvPathEastStepYCoords tail := by
  obtain ⟨tail', heq⟩ := hhead
  subst heq
  simp only [lgvPathEastStepYCoords]
  simp only [and_self, ↓reduceIte]

/-- Main induction lemma: lgvPathEastStepYCoords extracts the heights from buildVerticesAux. -/
lemma lgvPathEastStepYCoords_buildVerticesAux (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (hfuel : fuel ≥ heights.length + (N - y.toNat)) (hy : 1 ≤ y) (hyN : y ≤ N)
    (hchain : heights.IsChain (· ≤ ·))
    (hbounds : ∀ h ∈ heights, y ≤ (h.val : ℤ) + 1) :
    lgvPathEastStepYCoords (buildVerticesAux N x y heights fuel) =
      heights.map (fun h => (h.val : ℤ) + 1) := by
  induction fuel generalizing x y heights with
  | zero =>
    simp only [buildVerticesAux, lgvPathEastStepYCoords]
    have hlen : heights.length = 0 := by omega
    cases heights with
    | nil => rfl
    | cons _ _ => simp at hlen
  | succ n ih =>
    cases heights with
    | nil =>
      simp only [List.map_nil]
      by_cases hy_lt : y < (N : ℤ)
      · simp only [buildVerticesAux, hy_lt, ↓reduceIte]
        have hhead := buildVerticesAux_head' N x (y + 1) [] n
        rw [lgvPathEastStepYCoords_cons_north_gen x y _ hhead]
        -- Apply IH
        have hy_pos : 0 ≤ y := by omega
        have h1 : (y + 1).toNat = y.toNat + 1 := by
          have := Int.toNat_of_nonneg hy_pos; omega
        have hfuel' : n ≥ ([] : List (Fin N)).length + (N - (y + 1).toNat) := by
          simp only [List.length_nil, zero_add] at hfuel ⊢
          rw [h1]; omega
        exact ih x (y + 1) [] hfuel' (by omega) (by omega) List.isChain_nil (by simp)
      · simp only [buildVerticesAux, hy_lt, ↓reduceIte, lgvPathEastStepYCoords]
    | cons h rest =>
      by_cases hy_lt : y < (h.val : ℤ) + 1
      · -- North step case
        simp only [buildVerticesAux, hy_lt, ↓reduceIte]
        have hhead := buildVerticesAux_head' N x (y + 1) (h :: rest) n
        rw [lgvPathEastStepYCoords_cons_north_gen x y _ hhead]
        -- Apply IH
        have hy_pos : 0 ≤ y := by omega
        have h1 : (y + 1).toNat = y.toNat + 1 := by
          have := Int.toNat_of_nonneg hy_pos; omega
        have hfuel' : n ≥ (h :: rest).length + (N - (y + 1).toNat) := by
          simp only [List.length_cons] at hfuel ⊢
          rw [h1]
          have hle : y.toNat < N := by
            have hh := h.isLt
            have : y < N := by omega
            have htonat : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy_pos
            omega
          omega
        have hbounds' : ∀ h' ∈ (h :: rest), (y + 1) ≤ (h'.val : ℤ) + 1 := by
          intro h' hmem
          cases List.mem_cons.mp hmem with
          | inl heq => subst heq; omega
          | inr hrest =>
            have hrel : h ≤ h' := hchain.rel_cons hrest
            have : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
            omega
        have hyN' : y + 1 ≤ N := by have hh := h.isLt; omega
        exact ih x (y + 1) (h :: rest) hfuel' (by omega) hyN' hchain hbounds'
      · -- East step case: y ≥ h.val + 1
        simp only [buildVerticesAux, hy_lt, ↓reduceIte]
        have hhead := buildVerticesAux_head' N (x + 1) y rest n
        rw [lgvPathEastStepYCoords_cons_east_gen x y _ hhead]
        simp only [List.map_cons]
        have hy_eq : y = (h.val : ℤ) + 1 := by
          have hb := hbounds h List.mem_cons_self
          omega
        rw [hy_eq]
        congr 1
        -- Apply IH for rest
        have hfuel' : n ≥ rest.length + (N - y.toNat) := by
          simp only [List.length_cons] at hfuel
          omega
        have hchain' : rest.IsChain (· ≤ ·) := hchain.tail
        have hbounds' : ∀ h' ∈ rest, y ≤ (h'.val : ℤ) + 1 := by
          intro h' hmem
          have hrel : h ≤ h' := hchain.rel_cons hmem
          have h_ge : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
          have hb := hbounds h List.mem_cons_self
          omega
        rw [← hy_eq]
        exact ih (x + 1) y rest hfuel' hy hyN hchain' hbounds'

/-- Key lemma for surjectivity: the east-step y-coordinates of buildVertices equal
    the input heights shifted by 1.

    This is the inverse direction of the lgvPathToLatticePath bijection:
    building an LGV path from a LatticePath's heights and extracting the heights back
    gives the original heights.

    The proof requires showing that buildVerticesAux produces east-steps exactly at
    the heights h.val + 1 for each h in the input list. -/
lemma lgvPathEastStepYCoords_buildVertices (a c : ℤ) (heights : List (Fin N))
    (_hN : 0 < N) (hlen : heights.length = (c - a).toNat) (_h : 0 ≤ c - a)
    (hchain : heights.IsChain (· ≤ ·)) :
    lgvPathEastStepYCoords (buildVertices a c N heights) =
      heights.map (fun h => (h.val : ℤ) + 1) := by
  -- Apply the auxiliary lemma with appropriate parameters
  unfold buildVertices
  apply lgvPathEastStepYCoords_buildVerticesAux
  · -- hfuel: (c - a).toNat + N ≥ heights.length + (N - 1.toNat)
    simp only [Int.toNat_one]
    rw [hlen]
    omega
  · -- hy: 1 ≤ 1
    omega
  · -- hyN: 1 ≤ N
    omega
  · -- hchain
    exact hchain
  · -- hbounds: all heights have h.val ≥ 0, so 1 ≤ h.val + 1
    intro h' _
    have hh := h'.isLt
    omega

/-- The LGV path weight sum equals the LatticePath weight sum.
    This is proved using lgvPathToLatticePath as a bijection.

    The proof establishes that lgvPathToLatticePath is a bijection by showing:
    1. Injectivity: paths with the same east-step heights are equal
    2. Surjectivity: every LatticePath corresponds to an LGV path
    3. Weight preservation: lgvPathToLatticePath_weight_eq

    The bijection works because:
    - A path from (a, 1) to (c, N) is uniquely determined by its east-step heights
    - East-step heights form a weakly increasing sequence of length (c - a)
    - This is exactly the data in a LatticePath -/
lemma lgv_pathWeightSum_eq_latticePathSum (a c : ℤ) (h : 0 ≤ c - a) (hN : 0 < N) :
    LGV.pathWeightSum LGV.integerLattice_pathFinite (jacobiTrudiArcWeight (N := N) (R := R))
      (a, 1) (c, (N : ℤ)) = ∑ lp : LatticePath (N := N) a c, lp.weight (R := R) := by
  -- Both sides are sums over equivalent combinatorial objects.
  -- We use Finset.sum_bij with lgvPathToLatticePath.
  unfold LGV.pathWeightSum
  apply Finset.sum_bij
    (i := fun p hp => lgvPathToLatticePath a c p
      (by simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp; exact hp.1)
      (by simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp; exact hp.2))
    (hi := fun _ _ => Finset.mem_univ _)
    (i_inj := fun p₁ hp₁ p₂ hp₂ heq => by
        -- Injectivity: Use lgvPathToLatticePath_injective
        simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp₁ hp₂
        exact lgvPathToLatticePath_injective a c p₁ p₂ hp₁.1 hp₁.2 hp₂.1 hp₂.2 heq)
    (i_surj := fun lp _ => by
      -- Surjectivity: every LatticePath comes from some LGV path
      -- We construct the LGV path from lp.eastStepHeights using buildVertices.
      let vertices := buildVertices a c N lp.eastStepHeights
      have hne := buildVertices_nonempty a c N lp.eastStepHeights
      have harcs := buildVertices_arcs_valid a c N lp.eastStepHeights hN lp.length_eq h
      have hstart := buildVertices_head a c N lp.eastStepHeights hN
      have hfinish := buildVertices_getLast a c N lp.eastStepHeights hN lp.length_eq h lp.weaklyIncreasing
      -- Construct the path
      let p : LGV.SimpleDigraph.Path LGV.integerLattice := ⟨vertices, hne, harcs⟩
      use p
      -- Goal is: p ∈ pathsFromTo ∧ lgvPathToLatticePath p = lp
      refine ⟨?_, ?_⟩
      · -- Show p is in pathsFromTo
        simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        exact ⟨hstart, hfinish⟩
      · -- Show lgvPathToLatticePath p = lp
        -- Use lgvPathEastStepYCoords_buildVertices to show the east-step heights match
        apply LatticePath.ext
        simp only [lgvPathToLatticePath]
        -- Need to show: lgvYCoordsToFinN (lgvPathEastStepYCoords vertices) h' = lp.eastStepHeights
        -- where vertices = buildVertices a c N lp.eastStepHeights
        -- By lgvPathEastStepYCoords_buildVertices:
        --   lgvPathEastStepYCoords vertices = lp.eastStepHeights.map (fun h => h.val + 1)
        -- Then lgvYCoordsToFinN converts back to lp.eastStepHeights
        have heq := lgvPathEastStepYCoords_buildVertices a c lp.eastStepHeights hN lp.length_eq h lp.weaklyIncreasing
        -- Use lgvYCoordsToFinN_map_val_add_one_eq to complete the proof
        exact lgvYCoordsToFinN_map_val_add_one_eq lp.eastStepHeights heq _)
    (h := fun p hp => by
      simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp
      exact lgvPathToLatticePath_weight_eq a c p hp.1 hp.2)

/-- Key infrastructure lemma: The LGV path weight sum from (a, 1) to (c, N) with
    jacobiTrudiArcWeight equals hsymmExt(c - a).

    This connects the LGV framework (using SimpleDigraph.Path in integerLattice)
    to our LatticePath representation (using eastStepHeights).

    The proof uses lgv_pathWeightSum_eq_latticePathSum to establish a weight-preserving
    bijection between LGV paths and LatticePaths, then applies pathWeightSum_eq_hsymm.

    This is a key infrastructure lemma needed for det_jacobiTrudiMatrixH_eq_nipatSum. -/
lemma lgv_pathWeightSum_eq_hsymmExt (a c : ℤ) (hN : 0 < N) :
    LGV.pathWeightSum LGV.integerLattice_pathFinite (jacobiTrudiArcWeight (N := N) (R := R))
      (a, 1) (c, (N : ℤ)) = hsymmExt (N := N) (R := R) (c - a) := by
  by_cases h : 0 ≤ c - a
  · -- Case c - a ≥ 0: Use lgv_pathWeightSum_eq_latticePathSum and pathWeightSum_eq_hsymm
    rw [lgv_pathWeightSum_eq_latticePathSum a c h hN]
    have hpath := pathWeightSum_eq_hsymm (N := N) (R := R) a c
    unfold latticePathFinset at hpath
    simp only [h, ↓reduceIte] at hpath
    exact hpath
  · -- Case c - a < 0: both sides are 0
    push Not at h
    unfold hsymmExt
    simp only [Int.not_le.mpr h, ↓reduceIte]
    unfold LGV.pathWeightSum
    have hempty : LGV.pathsFromTo LGV.integerLattice LGV.integerLattice_pathFinite
        (a, 1) (c, ↑N) = ∅ := by
      ext p
      simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      constructor
      · intro ⟨hstart, hfinish⟩
        have hle : p.start.1 ≤ p.finish.1 := by
          have hne := p.nonempty
          have hlen : 0 < p.vertices.length := List.length_pos_of_ne_nil hne
          suffices ∀ i j : ℕ, (hi : i < p.vertices.length) → (hj : j < p.vertices.length) →
              i ≤ j → (p.vertices.get ⟨i, hi⟩).1 ≤ (p.vertices.get ⟨j, hj⟩).1 by
            have hlast : p.vertices.length - 1 < p.vertices.length :=
              Nat.sub_lt hlen Nat.one_pos
            have h := this 0 (p.vertices.length - 1) hlen hlast (Nat.zero_le _)
            simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at h ⊢
            convert h using 2 <;> simp [List.head_eq_getElem, List.getLast_eq_getElem]
          intro i j hi hj hij
          induction j with
          | zero => simp_all
          | succ k ih =>
            by_cases hik : i = k + 1
            · simp [hik]
            · have hik' : i ≤ k := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hij hik)
              have hk : k < p.vertices.length := Nat.lt_of_succ_lt hj
              have h1 := ih hk hik'
              have harc := p.arcs_valid k hj
              simp only [LGV.integerLattice] at harc
              rcases harc with ⟨hx, _⟩ | ⟨hx, _⟩
              · omega
              · omega
        rw [hstart, hfinish] at hle
        omega
      · intro hp
        simp at hp
    rw [hempty]
    simp

/-- The Jacobi-Trudi matrix is the transpose of the LGV path weight matrix.

    This is a key step in the proof of det_jacobiTrudiMatrixH_eq_nipatSum.
    The (i,j) entry of jacobiTrudiMatrixH is h_{λᵢ - μⱼ - i + j}, which equals
    the path weight sum from source A_j to target B_i. This is exactly the (j,i)
    entry of the path weight matrix, hence the transpose relationship.

    The proof uses lgv_pathWeightSum_eq_hsymmExt to connect the LGV path weight sum
    to hsymmExt, which is how jacobiTrudiMatrixH entries are defined. -/
lemma jacobiTrudiMatrixH_eq_pathWeightMatrix_transpose (lam mu : Fin N → ℕ) :
    jacobiTrudiMatrixH (R := R) lam mu =
      (LGV.pathWeightMatrix LGV.integerLattice_pathFinite
        (jacobiTrudiArcWeight (N := N) (R := R))
        (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam))ᵀ := by
  ext i j
  rw [jacobiTrudiMatrixH_eq_pathLength]
  simp only [Matrix.transpose_apply, LGV.pathWeightMatrix, Matrix.of_apply]
  simp only [jacobiTrudiSourceVertex, jacobiTrudiTargetVertex]
  -- Since i : Fin N exists, we have N > 0
  have hN : 0 < N := Fin.pos i
  rw [← lgv_pathWeightSum_eq_hsymmExt _ _ hN]

/-- Corollary: The determinant of jacobiTrudiMatrixH equals the determinant of the
    path weight matrix. This follows from det(Mᵀ) = det(M). -/
lemma det_jacobiTrudiMatrixH_eq_det_pathWeightMatrix (lam mu : Fin N → ℕ) :
    (jacobiTrudiMatrixH (R := R) lam mu).det =
      (LGV.pathWeightMatrix LGV.integerLattice_pathFinite
        (jacobiTrudiArcWeight (N := N) (R := R))
        (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam)).det := by
  rw [jacobiTrudiMatrixH_eq_pathWeightMatrix_transpose, Matrix.det_transpose]


/-- Helper lemma: If two non-intersecting paths have one path above the other at some sum value,
    the upper path stays above at all subsequent sum values.

    This is a key lemma for proving column-strictness from non-intersection.
    The proof uses discrete IVT: if the y-difference ever becomes ≤ 0, there must be
    a point where it equals 0, meaning the paths share a vertex (contradiction). -/
lemma path_above_stays_above (p p' : LGV.SimpleDigraph.Path LGV.integerLattice)
    (hni : ∀ v, v ∈ p.vertices → v ∉ p'.vertices)
    (s₀ : ℤ) -- the sum value (x + y) where p' is above p
    -- Indices for both paths at sum s₀
    (hs₀_p : s₀ ≥ p.start.1 + p.start.2)
    (hs₀_p' : s₀ ≥ p'.start.1 + p'.start.2)
    (hs₀_p_end : s₀ ≤ p.finish.1 + p.finish.2)
    (hs₀_p'_end : s₀ ≤ p'.finish.1 + p'.finish.2)
    -- p' is strictly above p at s₀
    (h_above : ∀ (hidx_p : (s₀ - p.start.1 - p.start.2).toNat < p.vertices.length)
               (hidx_p' : (s₀ - p'.start.1 - p'.start.2).toNat < p'.vertices.length),
               (p'.vertices.get ⟨(s₀ - p'.start.1 - p'.start.2).toNat, hidx_p'⟩).2 >
               (p.vertices.get ⟨(s₀ - p.start.1 - p.start.2).toNat, hidx_p⟩).2)
    -- A later sum value s₁
    (s₁ : ℤ) (hs₁ : s₁ ≥ s₀)
    (hs₁_p_end : s₁ ≤ p.finish.1 + p.finish.2)
    (hs₁_p'_end : s₁ ≤ p'.finish.1 + p'.finish.2) :
    ∀ (hidx_p : (s₁ - p.start.1 - p.start.2).toNat < p.vertices.length)
      (hidx_p' : (s₁ - p'.start.1 - p'.start.2).toNat < p'.vertices.length),
      (p'.vertices.get ⟨(s₁ - p'.start.1 - p'.start.2).toNat, hidx_p'⟩).2 >
      (p.vertices.get ⟨(s₁ - p.start.1 - p.start.2).toNat, hidx_p⟩).2 := by
  intro hidx_p hidx_p'
  -- Define the y-difference function: diff(s) = y_p'(s) - y_p(s)
  -- At s₀, diff > 0. If diff ever becomes ≤ 0, by discrete IVT there's a point where diff = 0,
  -- meaning both paths have the same (x, y), contradicting non-intersection.
  by_contra h_not_above
  push Not at h_not_above
  -- Define y-coordinate functions for each path at a given sum value
  let y_p (s : ℤ) : ℤ :=
    let idx := (s - p.start.1 - p.start.2).toNat
    if h : idx < p.vertices.length then (p.vertices.get ⟨idx, h⟩).2 else 0
  let y_p' (s : ℤ) : ℤ :=
    let idx := (s - p'.start.1 - p'.start.2).toNat
    if h : idx < p'.vertices.length then (p'.vertices.get ⟨idx, h⟩).2 else 0
  let diff (s : ℤ) : ℤ := y_p' s - y_p s
  -- At s₀, diff > 0
  have hidx_p_s₀ : (s₀ - p.start.1 - p.start.2).toNat < p.vertices.length := by
    have hlen := LGV.integerLattice_path_length_eq p
    omega
  have hidx_p'_s₀ : (s₀ - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
    have hlen := LGV.integerLattice_path_length_eq p'
    omega
  have hdiff_s₀ : diff s₀ > 0 := by
    simp only [diff, y_p, y_p', hidx_p_s₀, hidx_p'_s₀, dite_true]
    exact sub_pos.mpr (h_above hidx_p_s₀ hidx_p'_s₀)
  -- At s₁, diff ≤ 0
  have hdiff_s₁ : diff s₁ ≤ 0 := by
    simp only [diff, y_p, y_p', hidx_p, hidx_p', dite_true]
    omega
  -- The difference function changes by at most 1 at each step
  have hdiff_step : ∀ s : ℤ, s₀ ≤ s → s < s₁ → |diff (s + 1) - diff s| ≤ 1 := by
    intro s hs_lo hs_hi
    simp only [diff, y_p, y_p']
    -- Both paths take steps of size 1 in y-coordinate
    have hs_p_lo : s ≥ p.start.1 + p.start.2 := le_trans hs₀_p hs_lo
    have hs_p_hi : s < p.finish.1 + p.finish.2 := by
      have := LGV.integerLattice_path_length_eq p
      omega
    have hs_p'_lo : s ≥ p'.start.1 + p'.start.2 := le_trans hs₀_p' hs_lo
    have hs_p'_hi : s < p'.finish.1 + p'.finish.2 := by
      have := LGV.integerLattice_path_length_eq p'
      omega
    have hidx_p_s : (s - p.start.1 - p.start.2).toNat < p.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p
      omega
    have hidx_p'_s : (s - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p'
      omega
    have hidx_p_s1 : (s + 1 - p.start.1 - p.start.2).toNat < p.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p
      omega
    have hidx_p'_s1 : (s + 1 - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p'
      omega
    simp only [hidx_p_s, hidx_p'_s, hidx_p_s1, hidx_p'_s1, dite_true]
    -- The y-coordinate changes by 0 or 1 at each step
    have heq_idx_p : (s + 1 - p.start.1 - p.start.2).toNat = (s - p.start.1 - p.start.2).toNat + 1 := by omega
    have heq_idx_p' : (s + 1 - p'.start.1 - p'.start.2).toNat = (s - p'.start.1 - p'.start.2).toNat + 1 := by omega
    have hstep_p_idx : (s - p.start.1 - p.start.2).toNat + 1 < p.vertices.length := by omega
    have hstep_p'_idx : (s - p'.start.1 - p'.start.2).toNat + 1 < p'.vertices.length := by omega
    have harc_p := p.arcs_valid (s - p.start.1 - p.start.2).toNat hstep_p_idx
    have harc_p' := p'.arcs_valid (s - p'.start.1 - p'.start.2).toNat hstep_p'_idx
    -- Each arc changes y by 0 or 1
    rcases harc_p with ⟨_, hy_p⟩ | ⟨_, hy_p⟩ <;>
    rcases harc_p' with ⟨_, hy_p'⟩ | ⟨_, hy_p'⟩ <;>
    · simp only [heq_idx_p, heq_idx_p', abs_le]
      constructor <;> omega
  -- Apply discrete IVT to get a point where diff = 0
  have hs₀_le_s₁ : s₀ ≤ s₁ := hs₁
  obtain ⟨s_eq, hs_eq_lo, hs_eq_hi, hdiff_eq⟩ := LGV.discrete_ivt hs₀_le_s₁ diff hdiff_step (le_of_lt hdiff_s₀) hdiff_s₁
  -- At s_eq, both paths have the same y-coordinate
  have hidx_p_seq : (s_eq - p.start.1 - p.start.2).toNat < p.vertices.length := by
    have hlen := LGV.integerLattice_path_length_eq p
    omega
  have hidx_p'_seq : (s_eq - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
    have hlen := LGV.integerLattice_path_length_eq p'
    omega
  simp only [diff, y_p, y_p', hidx_p_seq, hidx_p'_seq, dite_true, sub_eq_zero] at hdiff_eq
  -- Both paths have the same sum value at s_eq, so same x + y = s_eq
  have hsum_p := LGV.integerLattice_path_vertex_sum p (s_eq - p.start.1 - p.start.2).toNat hidx_p_seq
  have hsum_p' := LGV.integerLattice_path_vertex_sum p' (s_eq - p'.start.1 - p'.start.2).toNat hidx_p'_seq
  -- Since x + y = s_eq for both, and y_p = y_p', we have x_p = x_p'
  -- So both paths visit the same vertex (x, y)
  have hx_eq : (p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩).1 =
               (p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩).1 := by
    omega
  have hy_eq : (p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩).2 =
               (p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩).2 := by
    omega
  -- The vertices are equal
  have hv_eq : p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩ =
               p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩ :=
    Prod.ext hx_eq hy_eq
  -- This contradicts non-intersection
  have hmem_p : p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩ ∈ p.vertices :=
    List.get_mem p.vertices ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩
  have hmem_p' : p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩ ∈ p'.vertices :=
    List.get_mem p'.vertices ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩
  rw [hv_eq] at hmem_p
  exact hni _ hmem_p hmem_p'

/-- Weight preservation: The LGV pathTupleWeight equals the Nipat weight under conversion. -/
lemma pathTupleToNipat_weight (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i)
    (pt : LGV.PathTuple LGV.integerLattice N
      (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam))
    (hni : pt.isNonIntersecting) :
    LGV.pathTupleWeight (jacobiTrudiArcWeight (N := N) (R := R)) pt.paths =
      (pathTupleToNipat lam mu hlam hmu hcontained pt hni).weight (R := R) := by
  -- The weight of a PathTuple is ∏ᵢ pathWeight(pᵢ)
  -- The weight of a Nipat is ∏ᵢ (paths i).weight
  -- By lgvPathToLatticePath_weight_eq, these are equal for each path
  unfold LGV.pathTupleWeight Nipat.weight pathTupleToNipat pathTupleToLatticePaths
  simp only
  apply Finset.prod_congr rfl
  intro i _
  exact lgvPathToLatticePath_weight_eq
    ((mu i : ℤ) - (i.val : ℤ))
    ((lam i : ℤ) - (i.val : ℤ))
    (pt.paths i)
    (by unfold jacobiTrudiSourceVertex jacobiTrudiSourceX at pt; exact pt.starts i)
    (by unfold jacobiTrudiTargetVertex jacobiTrudiTargetX at pt; exact pt.finishes i)

/-- The LGV nipat weight sum equals our Nipat weight sum.

    This connects the two representations of non-intersecting path tuples:
    - LGV: `PathTuple` with `isNonIntersecting` (no shared vertices)
    - Ours: `Nipat` with `colStrictPaths` (column-strictness)

    The bijection works as follows:
    - An LGV path from (a, 1) to (c, N) is encoded by its east-step heights
    - This is exactly our `LatticePath` type
    - Non-intersection of LGV paths ↔ column-strictness of east-step heights

    The proof uses `pathTupleToNipat` to convert LGV nipats to our Nipat type,
    with weight preservation via `pathTupleToNipat_weight`. -/
lemma lgv_nipatWeightSum_eq_nipatSum (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    LGV.nipatWeightSum LGV.integerLattice_pathFinite
      (jacobiTrudiArcWeight (N := N) (R := R))
      (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam) (Equiv.refl (Fin N)) =
    ∑ np : Nipat lam mu hlam hmu hcontained, np.weight (R := R) := by
  -- The proof establishes a weight-preserving bijection between:
  -- 1. LGV nipats: elements of nipatFinset with isNonIntersecting
  -- 2. Our Nipat: tuples of LatticePaths with colStrictPaths
  --
  -- Strategy: Use Finset.sum_bij with pathTupleToNipat as the bijection function.
  -- - pathTupleToNipat: converts non-intersecting PathTuples to Nipats
  -- - pathTupleToNipat_weight: proves weight preservation
  -- - Injectivity: follows from lgvPathToLatticePath being injective
  -- - Surjectivity: requires constructing the inverse (nipatToPathTuple)
  --
  -- Unfold the LHS
  unfold LGV.nipatWeightSum
  -- Use sum_bij to establish the equality
  refine Finset.sum_bij
    (fun pt hpt => pathTupleToNipat lam mu hlam hmu hcontained pt
      ((LGV.mem_nipatFinset_iff LGV.integerLattice_pathFinite pt).mp hpt))
    ?_ ?_ ?_ ?_
  -- 1. The function maps into Finset.univ
  · intro pt hpt
    exact Finset.mem_univ _
  -- 2. Injectivity: if pathTupleToNipat pt₁ = pathTupleToNipat pt₂, then pt₁ = pt₂
  · intro pt₁ hpt₁ pt₂ hpt₂ heq
    -- pathTupleToNipat extracts paths via pathTupleToLatticePaths, which uses lgvPathToLatticePath
    -- lgvPathToLatticePath extracts east-step heights, which uniquely determine the path
    -- Therefore, equal Nipats imply equal PathTuples
    have hpaths : (pathTupleToNipat lam mu hlam hmu hcontained pt₁
        ((LGV.mem_nipatFinset_iff LGV.integerLattice_pathFinite pt₁).mp hpt₁)).paths =
        (pathTupleToNipat lam mu hlam hmu hcontained pt₂
        ((LGV.mem_nipatFinset_iff LGV.integerLattice_pathFinite pt₂).mp hpt₂)).paths :=
      congr_arg Nipat.paths heq
    simp only [pathTupleToNipat] at hpaths
    -- hpaths : pathTupleToLatticePaths ... pt₁ = pathTupleToLatticePaths ... pt₂
    -- Need to show pt₁ = pt₂, i.e., pt₁.paths = pt₂.paths (as functions)
    ext i
    -- Goal: pt₁.paths i = pt₂.paths i
    have hi := congrFun hpaths i
    simp only [pathTupleToLatticePaths] at hi
    -- hi : lgvPathToLatticePath ... (pt₁.paths i) ... = lgvPathToLatticePath ... (pt₂.paths i) ...
    -- lgvPathToLatticePath extracts eastStepHeights
    -- Two paths with same start/end and same eastStepHeights are equal
    -- Use lgvPathToLatticePath_injective
    exact lgvPathToLatticePath_injective
      ((mu i : ℤ) - (i.val : ℤ))
      ((lam i : ℤ) - (i.val : ℤ))
      (pt₁.paths i) (pt₂.paths i)
      (by unfold jacobiTrudiSourceVertex jacobiTrudiSourceX at pt₁; exact pt₁.starts i)
      (by unfold jacobiTrudiTargetVertex jacobiTrudiTargetX at pt₁; exact pt₁.finishes i)
      (by unfold jacobiTrudiSourceVertex jacobiTrudiSourceX at pt₂; exact pt₂.starts i)
      (by unfold jacobiTrudiTargetVertex jacobiTrudiTargetX at pt₂; exact pt₂.finishes i)
      hi
  -- 3. Surjectivity: for every np : Nipat, there exists pt ∈ nipatFinset with pathTupleToNipat pt = np
  · intro np _
    -- We construct the inverse: given a Nipat, construct the corresponding PathTuple.
    -- For each path np.paths i : LatticePath, we build an LGV path using buildVertices.
    --
    -- First, we need N ≥ 1 for the buildVertices lemmas
    by_cases hN : N = 0
    · -- If N = 0, there are no Fin N elements
      subst hN
      -- Construct the trivial PathTuple (no paths)
      let pt : LGV.PathTuple LGV.integerLattice 0
          (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam) :=
        ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
      use pt
      refine ⟨?_, ?_⟩
      · -- pt is in nipatFinset
        simp only [LGV.mem_nipatFinset_iff, LGV.PathTuple.isNonIntersecting]
        exact fun i => Fin.elim0 i
      · -- pathTupleToNipat pt = np
        simp only [pathTupleToNipat]
        cases np with | mk paths colStrict =>
        congr 1
        funext i
        exact Fin.elim0 i
    · -- N ≥ 1
      have hN_pos : 0 < N := Nat.pos_of_ne_zero hN
      have hN_ge : N ≥ 1 := hN_pos
      -- For each i, construct the LGV path from np.paths i
      -- Define the path function
      let pathFn : (i : Fin N) → LGV.SimpleDigraph.Path LGV.integerLattice := fun i =>
        let lp := np.paths i
        let a := (mu i : ℤ) - (i.val : ℤ)
        let c := (lam i : ℤ) - (i.val : ℤ)
        let vertices := buildVertices a c N lp.eastStepHeights
        let hne := buildVertices_nonempty a c N lp.eastStepHeights
        -- Need to show c - a ≥ 0 for arcs_valid
        have h_ca : 0 ≤ c - a := by
          simp only [c, a]
          have hcont := hcontained i
          omega
        let harcs := buildVertices_arcs_valid a c N lp.eastStepHeights hN_pos lp.length_eq h_ca
        ⟨vertices, hne, harcs⟩
      -- Verify start conditions
      have hstarts : ∀ i, (pathFn i).start = jacobiTrudiSourceVertex mu i := fun i => by
        simp only [pathFn, LGV.SimpleDigraph.Path.start]
        have hne := buildVertices_nonempty ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ))
            N (np.paths i).eastStepHeights
        have h := buildVertices_head ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ))
            N (np.paths i).eastStepHeights hN_ge
        simp only [jacobiTrudiSourceVertex, jacobiTrudiSourceX]
        rw [← h]
      -- Verify finish conditions
      have hfinishes : ∀ i, (pathFn i).finish = jacobiTrudiTargetVertex lam i := fun i => by
        simp only [pathFn, LGV.SimpleDigraph.Path.finish]
        have h_ca : 0 ≤ ((lam i : ℤ) - (i.val : ℤ)) - ((mu i : ℤ) - (i.val : ℤ)) := by
          have hcont := hcontained i
          omega
        have hne := buildVertices_nonempty ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ))
            N (np.paths i).eastStepHeights
        have h := buildVertices_getLast ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ))
            N (np.paths i).eastStepHeights hN_pos (np.paths i).length_eq h_ca
            (np.paths i).weaklyIncreasing
        simp only [jacobiTrudiTargetVertex, jacobiTrudiTargetX]
        rw [← h]
      -- Construct the PathTuple
      let pt : LGV.PathTuple LGV.integerLattice N
          (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam) :=
        ⟨pathFn, hstarts, hfinishes⟩
      -- Show pt is non-intersecting
      have hni : pt.isNonIntersecting := by
        -- Non-intersection follows from column-strictness
        -- If paths i and j share a vertex (x, y), then at the same x-coordinate,
        -- both paths have the same y-coordinate. This means they have east-steps
        -- at the same column with the same height, violating column-strictness.
        intro i j hij hinter
        simp only [LGV.pathsIntersect] at hinter
        obtain ⟨⟨x, y⟩, hi_mem, hj_mem⟩ := hinter
        -- WLOG assume i < j (use lt_or_gt_of_ne)
        rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
        · -- Case i < j
          -- The shared vertex (x, y) means both paths pass through (x, y)
          -- This contradicts column-strictness via the following argument:
          --
          -- 1. Path i starts at (mu_i - i, 1), path j starts at (mu_j - j, 1)
          -- 2. Since mu is weakly decreasing and i < j, we have mu_i ≥ mu_j
          -- 3. Therefore mu_i - i > mu_j - j (path i starts to the RIGHT of path j)
          --
          -- 4. If (x, y) is shared, then x = (mu_i - i) + k_i = (mu_j - j) + k_j
          --    for some k_i < heights_i.length and k_j < heights_j.length
          -- 5. From mu_i - i > mu_j - j and x equal, we get k_i < k_j
          --
          -- 6. For buildVertices, at x-coordinate x = a + k:
          --    - The path has vertices with y in range [heights[k-1].val+1, heights[k].val+1]
          --    - Where heights[-1] is interpreted as 0 (so range starts at 1)
          --
          -- 7. For the ranges to overlap (sharing y), we need:
          --    heights_i[k_i].val + 1 ≥ heights_j[k_j-1].val + 1  (i's upper ≥ j's lower)
          --    heights_j[k_j].val + 1 ≥ heights_i[k_i-1].val + 1  (j's upper ≥ i's lower)
          --
          -- 8. But column-strictness at tableau column mu_i + k_i = mu_j + k_j - (j - i)
          --    gives constraints that make overlap impossible.
          --
          -- The proof uses the converse direction: isNonIntersecting_implies_colStrictPaths
          -- shows that non-intersection implies column-strictness. Here we show that
          -- column-strictness implies non-intersection by contrapositive.
          --
          -- Key insight: At x = mu_i - i (start of path i), path i is at y = 1.
          -- Path j at this x-coordinate must be at y > 1 (by column-strictness).
          -- Since both paths are monotone in y along x, and path j is above path i
          -- at x = mu_i - i, path j stays above path i at all shared x-coordinates.
          -- Therefore, they cannot share a vertex.
          exfalso
          -- Path i starts at (mu i - i, 1), ends at (lam i - i, N)
          have hstart_i : (pathFn i).start = ((mu i : ℤ) - (i.val : ℤ), 1) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.start]
            exact buildVertices_head _ _ N _ hN_ge
          have hfinish_i : (pathFn i).finish = ((lam i : ℤ) - (i.val : ℤ), (N : ℤ)) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.finish]
            have h_ca : 0 ≤ ((lam i : ℤ) - (i.val : ℤ)) - ((mu i : ℤ) - (i.val : ℤ)) := by
              have hcont := hcontained i; omega
            exact buildVertices_getLast _ _ N _ hN_pos (np.paths i).length_eq h_ca
                (np.paths i).weaklyIncreasing
          -- Path j starts at (mu j - j, 1), ends at (lam j - j, N)
          have hstart_j : (pathFn j).start = ((mu j : ℤ) - (j.val : ℤ), 1) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.start]
            exact buildVertices_head _ _ N _ hN_ge
          have hfinish_j : (pathFn j).finish = ((lam j : ℤ) - (j.val : ℤ), (N : ℤ)) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.finish]
            have h_ca : 0 ≤ ((lam j : ℤ) - (j.val : ℤ)) - ((mu j : ℤ) - (j.val : ℤ)) := by
              have hcont := hcontained j; omega
            exact buildVertices_getLast _ _ N _ hN_pos (np.paths j).length_eq h_ca
                (np.paths j).weaklyIncreasing
          -- Note: pt.paths = pathFn, so we can use hi_mem and hj_mem directly
          simp only [pt] at hi_mem hj_mem
          -- Get bounds on x for the shared vertex (x, y)
          -- From path i: mu_i - i ≤ x ≤ lam_i - i
          have hi_mem' := List.mem_iff_get.mp hi_mem
          obtain ⟨⟨idx_i, hidx_i⟩, heq_i⟩ := hi_mem'
          have hbd_i := LGV.integerLattice_path_vertices_bounded (pathFn i) idx_i hidx_i
          rw [hstart_i, hfinish_i] at hbd_i
          -- heq_i : (pathFn i).vertices.get ⟨idx_i, hidx_i⟩ = (x, y)
          have heq_i_x : ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).1 = x := by
            rw [heq_i]
          have heq_i_y : ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).2 = y := by
            rw [heq_i]
          have hx_lo_i : (mu i : ℤ) - (i.val : ℤ) ≤ x := by rw [← heq_i_x]; exact hbd_i.1
          have hx_hi_i : x ≤ (lam i : ℤ) - (i.val : ℤ) := by rw [← heq_i_x]; exact hbd_i.2.1
          -- From path j: mu_j - j ≤ x ≤ lam_j - j
          have hj_mem' := List.mem_iff_get.mp hj_mem
          obtain ⟨⟨idx_j, hidx_j⟩, heq_j⟩ := hj_mem'
          have hbd_j := LGV.integerLattice_path_vertices_bounded (pathFn j) idx_j hidx_j
          rw [hstart_j, hfinish_j] at hbd_j
          have heq_j_x : ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).1 = x := by
            rw [heq_j]
          have heq_j_y : ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).2 = y := by
            rw [heq_j]
          have hx_lo_j : (mu j : ℤ) - (j.val : ℤ) ≤ x := by rw [← heq_j_x]; exact hbd_j.1
          have hx_hi_j : x ≤ (lam j : ℤ) - (j.val : ℤ) := by rw [← heq_j_x]; exact hbd_j.2.1
          -- Case split: is path i a vertical line (lam_i = mu_i)?
          by_cases hvert : lam i = mu i
          · -- Case A: path i is vertical at x = mu_i - i
            -- From hx_lo_i and hx_hi_i with lam_i = mu_i: x = mu_i - i
            have hx_eq : x = (mu i : ℤ) - (i.val : ℤ) := by omega
            -- From hlam: lam_j ≤ lam_i = mu_i
            have hlam_j : lam j ≤ lam i := hlam i j (Fin.le_of_lt hij_lt)
            -- Since j > i and lam_j ≤ mu_i: lam_j - j < mu_i - i
            have hcontra : (lam j : ℤ) - (j.val : ℤ) < (mu i : ℤ) - (i.val : ℤ) := by
              omega
            -- But x ≤ lam_j - j and x = mu_i - i, contradiction
            omega
          · -- Case B: path i has east steps (lam_i > mu_i)
            -- Column-strictness ensures path j is above path i at their common x-range
            push Not at hvert
            have hlam_gt : lam i > mu i := Nat.lt_of_le_of_ne (hcontained i) (Ne.symm hvert)
            -- Path i starts strictly to the right of path j
            have hstart_lt : (mu j : ℤ) - (j.val : ℤ) < (mu i : ℤ) - (i.val : ℤ) := by
              have hmu_ij : mu j ≤ mu i := hmu i j (Fin.le_of_lt hij_lt)
              omega
            -- Key insight: At x = mu_i - i (start of path i), path i is at y = 1.
            -- Path j at this x must be at y > 1 by column-strictness.
            -- Using paths_above_at_x_stays_above, path j stays above path i at all x.
            -- But they share (x, y), so y_j = y_i = y, contradiction.
            --
            -- The proof requires showing that at any x where both paths have vertices,
            -- path j's y-coordinate is strictly greater than path i's y-coordinate.
            -- This follows from:
            -- 1. At x₀ = mu_i - i (start of path i), path i has y = 1
            -- 2. Path j at x₀ has y > 1 (by column-strictness: heights_j[m-1] > heights_i[0] ≥ 0)
            -- 3. By discrete IVT, if paths share (x, y) with x ≥ x₀, then the "above" property
            --    at x₀ combined with y_j = y_i at x implies paths share a vertex at some x' ≤ x.
            -- 4. This shared vertex contradicts the "above" property.
            --
            -- The detailed proof requires careful vertex analysis using buildVertices structure
            -- and the lgvPathEastStepYCoords lemmas. The key column-strictness argument:
            -- - At x₀, path j has taken m = (mu_i - mu_j) + (j - i) east steps
            -- - Column-strictness at column mu_i: heights_i[0] < heights_j[mu_i - mu_j]
            -- - Since m - 1 ≥ mu_i - mu_j and heights are weakly increasing:
            --   heights_j[m-1] ≥ heights_j[mu_i - mu_j] > heights_i[0] ≥ 0
            -- - So heights_j[m-1] ≥ 1, meaning path j is at y ≥ 2 > 1 at x₀
            --
            -- Detailed proof:
            -- The shared vertex (x, y) satisfies:
            -- - mu_i - i ≤ x ≤ lam_i - i (from path i bounds)
            -- - mu_j - j ≤ x ≤ lam_j - j (from path j bounds)
            -- Let k = x - (mu_i - i) be the number of east steps path i has taken to reach x.
            -- Let k' = x - (mu_j - j) be the number of east steps path j has taken to reach x.
            -- Then k' = k + (mu_i - mu_j) + (j - i).
            --
            -- At x, path i has y in range [heights_i[k-1].val + 1, heights_i[k].val + 1]
            -- (with heights_i[-1] = 0 for k = 0).
            -- At x, path j has y in range [heights_j[k'-1].val + 1, heights_j[k'].val + 1].
            --
            -- For paths to share y at x, these ranges must overlap:
            -- heights_j[k'-1].val + 1 ≤ heights_i[k].val + 1 (j's lower ≤ i's upper)
            --
            -- But by column-strictness (with tableau column mu_i + k = mu_j + (k' - (j - i))):
            -- heights_i[k] < heights_j[k' - (j - i)] = heights_j[(mu_i - mu_j) + k]
            --
            -- Since heights are weakly increasing and k' - 1 ≥ (mu_i - mu_j) + k:
            -- heights_j[k'-1] ≥ heights_j[(mu_i - mu_j) + k] > heights_i[k]
            --
            -- This contradicts heights_j[k'-1] ≤ heights_i[k] (from range overlap).
            --
            -- The technical challenge is extracting k from the vertex membership and
            -- relating it to the eastStepHeights structure. This requires the
            -- buildVertices_y_at_x infrastructure.
            --
            -- Proof using sum-based reasoning:
            -- At shared vertex (x, y), both paths have the same x + y value.
            -- The sum x + y = start_sum + idx, where idx is the vertex index.
            -- For path i: x + y = (mu_i - i + 1) + idx_i
            -- For path j: x + y = (mu_j - j + 1) + idx_j
            -- So idx_j - idx_i = (mu_i - mu_j) + (j - i)
            --
            -- The number of east steps k = x - start_x.
            -- For path i: k_i = x - (mu_i - i)
            -- For path j: k_j = x - (mu_j - j) = k_i + (mu_i - mu_j) + (j - i)
            --
            -- The y-coordinate y = 1 + (idx - k) (number of north steps + 1).
            -- Since y is the same for both: idx_i - k_i = idx_j - k_j = y - 1
            --
            -- Key constraint: at a vertex with k east steps and y-coordinate y,
            -- we have heights[k-1] < y - 1 ≤ heights[k] (for k > 0), or
            -- 0 ≤ y - 1 ≤ heights[0] (for k = 0).
            --
            -- For paths to share (x, y):
            -- - Path i: y - 1 ≤ heights_i[k_i] (upper bound)
            -- - Path j: y - 1 > heights_j[k_j - 1] (lower bound, for k_j > 0)
            --
            -- Actually, the constraint is: heights[k-1] + 1 ≤ y ≤ heights[k] + 1
            -- i.e., heights[k-1] ≤ y - 1 ≤ heights[k]
            --
            -- For overlap: heights_j[k_j-1] ≤ y - 1 ≤ heights_i[k_i]
            -- So heights_j[k_j-1] ≤ heights_i[k_i]
            --
            -- But by column-strictness: heights_i[k_i] < heights_j[k_i + (mu_i - mu_j)]
            -- And since k_j - 1 ≥ k_i + (mu_i - mu_j) and heights_j weakly increasing:
            -- heights_j[k_j-1] ≥ heights_j[k_i + (mu_i - mu_j)] > heights_i[k_i]
            -- Contradiction!
            --
            -- Define k_i and k_j
            let k_i := (x - ((mu i : ℤ) - (i.val : ℤ))).toNat
            let k_j := (x - ((mu j : ℤ) - (j.val : ℤ))).toNat
            -- Show k_j = k_i + (mu_i - mu_j) + (j - i)
            have hk_rel : k_j = k_i + (mu i - mu j) + (j.val - i.val) := by
              simp only [k_i, k_j]
              have hmu_ij : mu j ≤ mu i := hmu i j (Fin.le_of_lt hij_lt)
              have hx_ge_i : x ≥ (mu i : ℤ) - (i.val : ℤ) := hx_lo_i
              have hx_ge_j : x ≥ (mu j : ℤ) - (j.val : ℤ) := hx_lo_j
              omega
            -- Show k_i < heights_i.length
            have hk_i_lt : k_i < (np.paths i).eastStepHeights.length := by
              simp only [k_i]
              have hlen := (np.paths i).length_eq
              simp only [sub_sub_sub_cancel_right] at hlen
              have hcont := hcontained i
              have hx_hi : x ≤ (lam i : ℤ) - (i.val : ℤ) := hx_hi_i
              have hx_ge : x ≥ (mu i : ℤ) - (i.val : ℤ) := hx_lo_i
              -- x ≤ lam_j - j < lam_i - i (since lam_j ≤ lam_i and j > i)
              have hlam_ji : lam j ≤ lam i := hlam i j (Fin.le_of_lt hij_lt)
              have hx_lt : x < (lam i : ℤ) - (i.val : ℤ) := by
                have h1 : x ≤ (lam j : ℤ) - (j.val : ℤ) := hx_hi_j
                omega
              have hnneg : (lam i : ℤ) - (mu i : ℤ) ≥ 0 := by omega
              have hnneg2 : x - ((mu i : ℤ) - (i.val : ℤ)) ≥ 0 := by omega
              have hlt : x - ((mu i : ℤ) - (i.val : ℤ)) < (lam i : ℤ) - (mu i : ℤ) := by omega
              rw [hlen]
              have h1 : ((x - ((mu i : ℤ) - (i.val : ℤ))).toNat : ℤ) = x - ((mu i : ℤ) - (i.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg2
              have h2 : (((lam i : ℤ) - (mu i : ℤ)).toNat : ℤ) = (lam i : ℤ) - (mu i : ℤ) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Show k_i + (mu_i - mu_j) < heights_j.length (for column-strictness)
            have hk_col_lt : k_i + (mu i - mu j) < (np.paths j).eastStepHeights.length := by
              simp only [k_i]
              have hlen := (np.paths j).length_eq
              simp only [sub_sub_sub_cancel_right] at hlen
              have hx_hi : x ≤ (lam j : ℤ) - (j.val : ℤ) := hx_hi_j
              have hmu_ij : mu j ≤ mu i := hmu i j (Fin.le_of_lt hij_lt)
              have hcont := hcontained j
              have hx_ge : x ≥ (mu i : ℤ) - (i.val : ℤ) := hx_lo_i
              have hnneg : (lam j : ℤ) - (mu j : ℤ) ≥ 0 := by omega
              have hnneg2 : x - ((mu i : ℤ) - (i.val : ℤ)) ≥ 0 := by omega
              have hlt : x - ((mu i : ℤ) - (i.val : ℤ)) + ((mu i : ℤ) - (mu j : ℤ)) < (lam j : ℤ) - (mu j : ℤ) := by omega
              rw [hlen]
              have h1 : ((x - ((mu i : ℤ) - (i.val : ℤ))).toNat : ℤ) = x - ((mu i : ℤ) - (i.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg2
              have h2 : (((lam j : ℤ) - (mu j : ℤ)).toNat : ℤ) = (lam j : ℤ) - (mu j : ℤ) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Show k_j > 0 (path j has taken at least one east step to reach x)
            have hk_j_pos : k_j > 0 := by
              simp only [k_j]
              have hx_ge : x ≥ (mu i : ℤ) - (i.val : ℤ) := hx_lo_i
              have hmu_ij : mu j ≤ mu i := hmu i j (Fin.le_of_lt hij_lt)
              omega
            -- Show k_j - 1 ≥ k_i + (mu_i - mu_j)
            have hk_j_ge : k_j - 1 ≥ k_i + (mu i - mu j) := by
              rw [hk_rel]
              have hij_pos : j.val - i.val ≥ 1 := Nat.sub_pos_of_lt hij_lt
              omega
            -- Apply column-strictness at column mu_i + k_i
            have hcol_eq : mu i + k_i = mu j + (k_i + (mu i - mu j)) := by
              have hmu_ij : mu j ≤ mu i := hmu i j (Fin.le_of_lt hij_lt)
              omega
            have hcolstrict := np.colStrictPaths i j hij_lt k_i hk_i_lt
                (k_i + (mu i - mu j)) hk_col_lt hcol_eq
            -- Apply weakly increasing property of heights_j
            have hk_j_lt : k_j - 1 < (np.paths j).eastStepHeights.length := by
              have hlen : (np.paths j).eastStepHeights.length = lam j - mu j := by
                have h := (np.paths j).length_eq
                simp only [sub_sub_sub_cancel_right] at h
                have hcont := hcontained j
                omega
              rw [hlen]
              simp only [k_j]
              have hx_hi : x ≤ (lam j : ℤ) - (j.val : ℤ) := hx_hi_j
              have hcont := hcontained j
              omega
            have hweakly := List.IsChain.getElem_le_getElem_of_le (np.paths j).weaklyIncreasing
                hk_col_lt hk_j_lt hk_j_ge
            -- Derive: heights_j[k_j-1] > heights_i[k_i]
            have hcontra : (np.paths j).eastStepHeights[k_j - 1] > (np.paths i).eastStepHeights[k_i] :=
              lt_of_lt_of_le hcolstrict hweakly
            -- Now we need to show this contradicts the shared vertex
            -- The shared vertex (x, y) requires y to be in both paths' y-ranges
            -- For path i at x: y ≤ heights_i[k_i] + 1
            -- For path j at x: y > heights_j[k_j-1] + 1 (actually y ≥ heights_j[k_j-1] + 1)
            --
            -- Wait, the ranges are:
            -- Path i at x: heights_i[k_i-1] + 1 ≤ y ≤ heights_i[k_i] + 1
            -- Path j at x: heights_j[k_j-1] + 1 ≤ y ≤ heights_j[k_j] + 1
            --
            -- For overlap: heights_j[k_j-1] + 1 ≤ heights_i[k_i] + 1
            -- i.e., heights_j[k_j-1] ≤ heights_i[k_i]
            --
            -- But hcontra says heights_j[k_j-1] > heights_i[k_i]
            -- So the ranges don't overlap, contradiction!
            --
            -- To formalize this, we need lemmas about the y-range at each x.
            -- For now, we use the sum-based approach with lgvPathEastStepYCoords.
            --
            -- At the shared vertex (x, y):
            -- - For path i: y is the y-coordinate at some vertex with x-coordinate x
            -- - The y-coordinate at the k_i-th east step is heights_i[k_i] + 1
            -- - All vertices at x have y ≤ heights_i[k_i] + 1
            --
            -- Similarly for path j: y ≥ heights_j[k_j-1] + 1 (for k_j > 0)
            --
            -- So heights_j[k_j-1] + 1 ≤ y ≤ heights_i[k_i] + 1
            -- i.e., heights_j[k_j-1] ≤ heights_i[k_i]
            --
            -- But hcontra says heights_j[k_j-1] > heights_i[k_i], contradiction!
            --
            -- The formal proof requires establishing the y-bounds, which needs
            -- additional lemmas about buildVertices. For now, we note that
            -- the key inequality hcontra is established, and the y-bound
            -- lemmas are the remaining infrastructure needed.
            --
            -- Use the sum-based reasoning to derive contradiction
            -- At shared vertex (x, y), both paths have sum x + y
            -- Path i: sum = (mu_i - i) + 1 + idx_i, so idx_i = x + y - (mu_i - i) - 1
            -- Path j: sum = (mu_j - j) + 1 + idx_j, so idx_j = x + y - (mu_j - j) - 1
            --
            -- The number of north steps is idx - k = (x + y - start - 1) - (x - start) = y - 1
            -- So at vertex (x, y), the path has taken y - 1 north steps.
            --
            -- The constraint from buildVertices:
            -- After k east steps and n north steps (n = idx - k = y - 1), we have:
            -- - The k-th east step happens at y = heights[k] + 1
            -- - So after k east steps, y ≤ heights[k] + 1, i.e., y - 1 ≤ heights[k]
            -- - Before the k-th east step (if k > 0), y ≥ heights[k-1] + 1, i.e., y - 1 ≥ heights[k-1]
            --
            -- For path i at (x, y): y - 1 ≤ heights_i[k_i]
            -- For path j at (x, y): y - 1 ≥ heights_j[k_j - 1] (since k_j > 0)
            --
            -- So heights_j[k_j - 1] ≤ y - 1 ≤ heights_i[k_i]
            -- This gives heights_j[k_j - 1] ≤ heights_i[k_i]
            --
            -- But hcontra says heights_j[k_j - 1] > heights_i[k_i]
            -- Contradiction!
            --
            -- To formalize, we need to prove:
            -- 1. For path i at (x, y): (y - 1).toNat ≤ heights_i[k_i].val
            -- 2. For path j at (x, y): heights_j[k_j - 1].val ≤ (y - 1).toNat
            --
            -- These follow from the buildVertices structure, but require careful
            -- analysis. For now, we use omega to derive the contradiction from
            -- the established inequalities.
            --
            -- The y-coordinate y satisfies 1 ≤ y ≤ N (from path bounds)
            have hy_ge : y ≥ 1 := by
              have hbd := LGV.integerLattice_path_vertices_bounded (pathFn i) idx_i hidx_i
              have h := hbd.2.2.1
              rw [hstart_i] at h
              rw [heq_i_y] at h
              exact h
            have hy_le : y ≤ N := by
              have hbd := LGV.integerLattice_path_vertices_bounded (pathFn i) idx_i hidx_i
              have h := hbd.2.2.2
              rw [hfinish_i] at h
              rw [heq_i_y] at h
              exact h
            -- The y-1 value is in [0, N-1], which is the range of Fin N values
            -- heights_i[k_i] and heights_j[k_j-1] are Fin N values
            -- We need to show: heights_j[k_j-1].val > heights_i[k_i].val
            -- This follows directly from hcontra (Fin comparison is by val)
            have hval_contr : (np.paths j).eastStepHeights[k_j - 1].val >
                              (np.paths i).eastStepHeights[k_i].val := hcontra
            -- Apply y-bound lemmas to derive contradiction
            -- For path i at (x, y): y ≤ heights_i[k_i].val + 1
            -- For path j at (x, y): y ≥ heights_j[k_j-1].val + 1
            --
            -- Set up for buildVertices_y_upper_bound_at_x on path i
            let a_i := (mu i : ℤ) - (i.val : ℤ)
            let c_i := (lam i : ℤ) - (i.val : ℤ)
            have h_ca_i : 0 ≤ c_i - a_i := by
              simp only [c_i, a_i]; have hcont := hcontained i; omega
            -- (pathFn i).vertices = buildVertices a_i c_i N (np.paths i).eastStepHeights
            have hvertices_i : (pathFn i).vertices = buildVertices a_i c_i N (np.paths i).eastStepHeights := by
              simp only [pathFn, a_i, c_i]
            -- hidx_i : idx_i < (pathFn i).vertices.length
            have hidx_i' : idx_i < (buildVertices a_i c_i N (np.paths i).eastStepHeights).length := by
              rw [← hvertices_i]; exact hidx_i
            -- heq_i_x says ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).1 = x
            -- We need: (buildVertices a_i c_i N heights_i)[idx_i].1 = a_i + k_i
            have hx_eq_i : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].1 = a_i + k_i := by
              have h1 : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].1 =
                  ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).1 := by
                simp only [hvertices_i, List.get_eq_getElem]
              rw [h1, heq_i_x]
              simp only [k_i, a_i]
              have hnneg : x - ((mu i : ℤ) - (i.val : ℤ)) ≥ 0 := by omega
              have h2 : ((x - ((mu i : ℤ) - (i.val : ℤ))).toNat : ℤ) = x - ((mu i : ℤ) - (i.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Apply buildVertices_y_upper_bound_at_x
            have hy_upper : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].2 ≤
                ((np.paths i).eastStepHeights[k_i]).val + 1 :=
              buildVertices_y_upper_bound_at_x a_i c_i N (np.paths i).eastStepHeights hN_pos
                (np.paths i).length_eq h_ca_i (np.paths i).weaklyIncreasing idx_i hidx_i' k_i hk_i_lt hx_eq_i
            -- Convert to y ≤ heights_i[k_i].val + 1
            have hy_upper' : y ≤ ((np.paths i).eastStepHeights[k_i]).val + 1 := by
              have h1 : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].2 =
                  ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).2 := by
                simp only [hvertices_i, List.get_eq_getElem]
              rw [h1, heq_i_y] at hy_upper
              exact hy_upper
            -- Set up for buildVertices_y_lower_bound_at_x on path j
            let a_j := (mu j : ℤ) - (j.val : ℤ)
            let c_j := (lam j : ℤ) - (j.val : ℤ)
            have h_ca_j : 0 ≤ c_j - a_j := by
              simp only [c_j, a_j]; have hcont := hcontained j; omega
            have hvertices_j : (pathFn j).vertices = buildVertices a_j c_j N (np.paths j).eastStepHeights := by
              simp only [pathFn, a_j, c_j]
            have hidx_j' : idx_j < (buildVertices a_j c_j N (np.paths j).eastStepHeights).length := by
              rw [← hvertices_j]; exact hidx_j
            have hx_eq_j : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].1 = a_j + k_j := by
              have h1 : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].1 =
                  ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).1 := by
                simp only [hvertices_j, List.get_eq_getElem]
              rw [h1, heq_j_x]
              simp only [k_j, a_j]
              have hnneg : x - ((mu j : ℤ) - (j.val : ℤ)) ≥ 0 := by omega
              have h2 : ((x - ((mu j : ℤ) - (j.val : ℤ))).toNat : ℤ) = x - ((mu j : ℤ) - (j.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Need k_j < heights_j.length for the lower bound lemma
            -- We have k_j - 1 < heights_j.length from hk_j_lt
            -- If k_j = heights_j.length, then x = lam_j - j (endpoint of path j)
            -- At the endpoint, path j has y = N. But path i at x has y ≤ heights_i[k_i] + 1.
            -- Since x ≤ lam_i - i (from path i bounds) and lam_j - j < lam_i - i (from i < j, lam decreasing),
            -- if x = lam_j - j, then x < lam_i - i, so path i hasn't reached its endpoint.
            -- This means y < N for path i (since only the endpoint has y = N).
            -- Contradiction: y = N (from path j) and y < N (from path i).
            have hk_j_strict : k_j < (np.paths j).eastStepHeights.length := by
              have hlen : (np.paths j).eastStepHeights.length = lam j - mu j := by
                have h := (np.paths j).length_eq
                simp only [sub_sub_sub_cancel_right] at h
                have hcont := hcontained j
                omega
              rw [hlen]
              simp only [k_j]
              have hx_hi : x ≤ (lam j : ℤ) - (j.val : ℤ) := hx_hi_j
              have hcont := hcontained j
              have hnneg : (lam j : ℤ) - (mu j : ℤ) ≥ 0 := by omega
              have hnneg2 : x - ((mu j : ℤ) - (j.val : ℤ)) ≥ 0 := by omega
              by_cases hx_eq : x = (lam j : ℤ) - (j.val : ℤ)
              · -- If x = lam_j - j, derive contradiction
                exfalso
                -- At x = lam_j - j, k_j = heights_j.length
                have hk_j_eq : k_j = lam j - mu j := by
                  simp only [k_j, hx_eq]
                  have hnneg3 : (lam j : ℤ) - (j.val : ℤ) - ((mu j : ℤ) - (j.val : ℤ)) ≥ 0 := by omega
                  omega
                have hlen_j : (np.paths j).eastStepHeights.length = lam j - mu j := hlen
                -- Use the upper bound from path i: y ≤ heights_i[k_i] + 1
                have hy_upper_i := hy_upper'
                -- heights_j[k_j - 1] > heights_i[k_i]
                have hcontra_val : (np.paths j).eastStepHeights[k_j - 1].val > (np.paths i).eastStepHeights[k_i].val := hcontra
                -- At x = lam_j - j, k_j - 1 = heights_j.length - 1
                have hk_j_minus_1 : k_j - 1 = (np.paths j).eastStepHeights.length - 1 := by
                  rw [hk_j_eq, hlen_j]
                -- At x = lam_j - j, path j is in its last column
                -- All vertices in this column have y ≥ heights_j[last] + 1
                have hlen_pos : 0 < (np.paths j).eastStepHeights.length := by
                  rw [hlen_j]; omega
                have hy_ge_last : y ≥ ((np.paths j).eastStepHeights[(np.paths j).eastStepHeights.length - 1]).val + 1 := by
                  -- At x = a_j + heights_j.length, path j is in its last column
                  -- The y-coordinate is at least heights_j[last] + 1
                  -- Use buildVertices_y_lower_bound_at_last_column
                  have hx_eq_j_last : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].1 =
                      a_j + (np.paths j).eastStepHeights.length := by
                    have h1 : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].1 =
                        ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).1 := by
                      simp only [hvertices_j, List.get_eq_getElem]
                    rw [h1, heq_j_x, hx_eq]
                    simp only [a_j, hlen_j]
                    omega
                  have hy_lower_last := buildVertices_y_lower_bound_at_last_column a_j c_j N
                    (np.paths j).eastStepHeights hN_pos (np.paths j).length_eq h_ca_j
                    (np.paths j).weaklyIncreasing hlen_pos idx_j hidx_j' hx_eq_j_last
                  have h1 : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].2 =
                      ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).2 := by
                    simp only [hvertices_j, List.get_eq_getElem]
                  rw [h1, heq_j_y] at hy_lower_last
                  exact hy_lower_last
                have hcontra_val' : (np.paths j).eastStepHeights[(np.paths j).eastStepHeights.length - 1].val >
                    (np.paths i).eastStepHeights[k_i].val := by
                  have h : k_j - 1 = (np.paths j).eastStepHeights.length - 1 := hk_j_minus_1
                  simp only [h] at hcontra_val
                  exact hcontra_val
                omega
              · -- x < lam_j - j, so k_j < lam_j - mu_j = heights.length
                have hx_lt : x < (lam j : ℤ) - (j.val : ℤ) := by
                  have h := hx_hi; omega
                have h1 : ((x - ((mu j : ℤ) - (j.val : ℤ))).toNat : ℤ) = x - ((mu j : ℤ) - (j.val : ℤ)) :=
                  Int.toNat_of_nonneg hnneg2
                have h2 : (((lam j : ℤ) - (mu j : ℤ)).toNat : ℤ) = (lam j : ℤ) - (mu j : ℤ) :=
                  Int.toNat_of_nonneg hnneg
                omega
            -- Apply buildVertices_y_lower_bound_at_x
            have hy_lower : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].2 ≥
                ((np.paths j).eastStepHeights[k_j - 1]).val + 1 :=
              buildVertices_y_lower_bound_at_x a_j c_j N (np.paths j).eastStepHeights hN_pos
                (np.paths j).length_eq h_ca_j (np.paths j).weaklyIncreasing idx_j hidx_j' k_j hk_j_strict hk_j_pos hx_eq_j
            -- Convert to y ≥ heights_j[k_j-1].val + 1
            have hy_lower' : y ≥ ((np.paths j).eastStepHeights[k_j - 1]).val + 1 := by
              have h1 : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].2 =
                  ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).2 := by
                simp only [hvertices_j, List.get_eq_getElem]
              rw [h1, heq_j_y] at hy_lower
              exact hy_lower
            -- Combine: heights_j[k_j-1].val + 1 ≤ y ≤ heights_i[k_i].val + 1
            -- So heights_j[k_j-1].val ≤ heights_i[k_i].val
            -- But hval_contr says heights_j[k_j-1].val > heights_i[k_i].val
            omega
        · -- Case j < i: symmetric argument (swap i and j)
          exfalso
          -- Path j starts at (mu j - j, 1), ends at (lam j - j, N)
          have hstart_j : (pathFn j).start = ((mu j : ℤ) - (j.val : ℤ), 1) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.start]
            exact buildVertices_head _ _ N _ hN_ge
          have hfinish_j : (pathFn j).finish = ((lam j : ℤ) - (j.val : ℤ), (N : ℤ)) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.finish]
            have h_ca : 0 ≤ ((lam j : ℤ) - (j.val : ℤ)) - ((mu j : ℤ) - (j.val : ℤ)) := by
              have hcont := hcontained j; omega
            exact buildVertices_getLast _ _ N _ hN_pos (np.paths j).length_eq h_ca
                (np.paths j).weaklyIncreasing
          -- Path i starts at (mu i - i, 1), ends at (lam i - i, N)
          have hstart_i : (pathFn i).start = ((mu i : ℤ) - (i.val : ℤ), 1) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.start]
            exact buildVertices_head _ _ N _ hN_ge
          have hfinish_i : (pathFn i).finish = ((lam i : ℤ) - (i.val : ℤ), (N : ℤ)) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.finish]
            have h_ca : 0 ≤ ((lam i : ℤ) - (i.val : ℤ)) - ((mu i : ℤ) - (i.val : ℤ)) := by
              have hcont := hcontained i; omega
            exact buildVertices_getLast _ _ N _ hN_pos (np.paths i).length_eq h_ca
                (np.paths i).weaklyIncreasing
          -- Note: pt.paths = pathFn, so we can use hi_mem and hj_mem directly
          simp only [pt] at hi_mem hj_mem
          -- Get bounds on x for the shared vertex (x, y)
          -- From path j: mu_j - j ≤ x ≤ lam_j - j
          have hj_mem' := List.mem_iff_get.mp hj_mem
          obtain ⟨⟨idx_j, hidx_j⟩, heq_j⟩ := hj_mem'
          have hbd_j := LGV.integerLattice_path_vertices_bounded (pathFn j) idx_j hidx_j
          rw [hstart_j, hfinish_j] at hbd_j
          have heq_j_x : ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).1 = x := by
            rw [heq_j]
          have heq_j_y : ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).2 = y := by
            rw [heq_j]
          have hx_lo_j : (mu j : ℤ) - (j.val : ℤ) ≤ x := by rw [← heq_j_x]; exact hbd_j.1
          have hx_hi_j : x ≤ (lam j : ℤ) - (j.val : ℤ) := by rw [← heq_j_x]; exact hbd_j.2.1
          -- From path i: mu_i - i ≤ x ≤ lam_i - i
          have hi_mem' := List.mem_iff_get.mp hi_mem
          obtain ⟨⟨idx_i, hidx_i⟩, heq_i⟩ := hi_mem'
          have hbd_i := LGV.integerLattice_path_vertices_bounded (pathFn i) idx_i hidx_i
          rw [hstart_i, hfinish_i] at hbd_i
          have heq_i_x : ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).1 = x := by
            rw [heq_i]
          have heq_i_y : ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).2 = y := by
            rw [heq_i]
          have hx_lo_i : (mu i : ℤ) - (i.val : ℤ) ≤ x := by rw [← heq_i_x]; exact hbd_i.1
          have hx_hi_i : x ≤ (lam i : ℤ) - (i.val : ℤ) := by rw [← heq_i_x]; exact hbd_i.2.1
          -- Case split: is path j a vertical line (lam_j = mu_j)?
          by_cases hvert : lam j = mu j
          · -- Case A: path j is vertical at x = mu_j - j
            -- From hx_lo_j and hx_hi_j with lam_j = mu_j: x = mu_j - j
            have hx_eq : x = (mu j : ℤ) - (j.val : ℤ) := by omega
            -- From hlam: lam_i ≤ lam_j = mu_j
            have hlam_i : lam i ≤ lam j := hlam j i (Fin.le_of_lt hji_lt)
            -- Since i > j and lam_i ≤ mu_j: lam_i - i < mu_j - j
            have hcontra : (lam i : ℤ) - (i.val : ℤ) < (mu j : ℤ) - (j.val : ℤ) := by
              omega
            -- But x ≤ lam_i - i and x = mu_j - j, contradiction
            omega
          · -- Case B: path j has east steps (lam_j > mu_j)
            -- This case requires the path_above_stays_above infrastructure
            -- Column-strictness ensures path i is above path j at their common x-range
            push Not at hvert
            have hlam_gt : lam j > mu j := Nat.lt_of_le_of_ne (hcontained j) (Ne.symm hvert)
            -- Path j starts strictly to the right of path i
            have hstart_lt : (mu i : ℤ) - (i.val : ℤ) < (mu j : ℤ) - (j.val : ℤ) := by
              have hmu_ji : mu i ≤ mu j := hmu j i (Fin.le_of_lt hji_lt)
              omega
            -- The x-coordinate x is in the range where both paths overlap
            -- At x = mu_j - j (start of path j), path j is at y = 1
            -- Path i at this x must be at y > 1 by column-strictness
            -- Using path_above_stays_above, path i stays above path j
            -- But they share (x, y), so y_i = y_j = y, contradiction
            --
            -- Detailed proof (symmetric to Case i < j):
            -- The shared vertex (x, y) satisfies:
            -- - mu_j - j ≤ x ≤ lam_j - j (from path j bounds)
            -- - mu_i - i ≤ x ≤ lam_i - i (from path i bounds)
            -- Let k = x - (mu_j - j) be the number of east steps path j has taken to reach x.
            -- Let k' = x - (mu_i - i) be the number of east steps path i has taken to reach x.
            -- Then k' = k + (mu_j - mu_i) + (i - j).
            --
            -- At x, path j has y in range [heights_j[k-1].val + 1, heights_j[k].val + 1]
            -- (with heights_j[-1] = 0 for k = 0).
            -- At x, path i has y in range [heights_i[k'-1].val + 1, heights_i[k'].val + 1].
            --
            -- For paths to share y at x, these ranges must overlap:
            -- heights_i[k'-1].val + 1 ≤ heights_j[k].val + 1 (i's lower ≤ j's upper)
            --
            -- But by column-strictness (with j < i and tableau column mu_j + k = mu_i + (k' - (i - j))):
            -- heights_j[k] < heights_i[k' - (i - j)] = heights_i[(mu_j - mu_i) + k]
            --
            -- Since heights are weakly increasing and k' - 1 ≥ (mu_j - mu_i) + k:
            -- heights_i[k'-1] ≥ heights_i[(mu_j - mu_i) + k] > heights_j[k]
            --
            -- This contradicts heights_i[k'-1] ≤ heights_j[k] (from range overlap).
            --
            -- The technical challenge is extracting k from the vertex membership and
            -- relating it to the eastStepHeights structure. This requires the
            -- buildVertices_y_at_x infrastructure.
            --
            -- Symmetric proof to Case i < j:
            -- Define k_j and k_i (number of east steps for each path to reach x)
            let k_j := (x - ((mu j : ℤ) - (j.val : ℤ))).toNat
            let k_i := (x - ((mu i : ℤ) - (i.val : ℤ))).toNat
            -- Show k_i = k_j + (mu_j - mu_i) + (i - j)
            have hk_rel : k_i = k_j + (mu j - mu i) + (i.val - j.val) := by
              simp only [k_i, k_j]
              have hmu_ji : mu i ≤ mu j := hmu j i (Fin.le_of_lt hji_lt)
              have hx_ge_i : x ≥ (mu i : ℤ) - (i.val : ℤ) := hx_lo_i
              have hx_ge_j : x ≥ (mu j : ℤ) - (j.val : ℤ) := hx_lo_j
              have h1 : ((x - ((mu i : ℤ) - (i.val : ℤ))).toNat : ℤ) = x - ((mu i : ℤ) - (i.val : ℤ)) :=
                Int.toNat_of_nonneg (by omega)
              have h2 : ((x - ((mu j : ℤ) - (j.val : ℤ))).toNat : ℤ) = x - ((mu j : ℤ) - (j.val : ℤ)) :=
                Int.toNat_of_nonneg (by omega)
              omega
            -- Show k_j < heights_j.length (path j hasn't finished all east steps)
            -- In the j < i case, we have x ≤ lam_i - i < lam_j - j (since lam_i ≤ lam_j and i > j)
            -- So x < lam_j - j, which means k_j < heights_j.length
            have hk_j_lt : k_j < (np.paths j).eastStepHeights.length := by
              have hlen : (np.paths j).eastStepHeights.length = lam j - mu j := by
                have h := (np.paths j).length_eq
                simp only [sub_sub_sub_cancel_right] at h
                have hcont := hcontained j
                omega
              rw [hlen]
              simp only [k_j]
              have hx_hi : x ≤ (lam i : ℤ) - (i.val : ℤ) := hx_hi_i
              have hlam_ji : lam i ≤ lam j := hlam j i (Fin.le_of_lt hji_lt)
              have hcont := hcontained j
              have hnneg : (lam j : ℤ) - (mu j : ℤ) ≥ 0 := by omega
              have hnneg2 : x - ((mu j : ℤ) - (j.val : ℤ)) ≥ 0 := by omega
              -- Key: x ≤ lam_i - i < lam_j - j
              have hx_lt_lam_j : x < (lam j : ℤ) - (j.val : ℤ) := by omega
              have h1 : ((x - ((mu j : ℤ) - (j.val : ℤ))).toNat : ℤ) = x - ((mu j : ℤ) - (j.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg2
              have h2 : (((lam j : ℤ) - (mu j : ℤ)).toNat : ℤ) = (lam j : ℤ) - (mu j : ℤ) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Show k_j + (mu_j - mu_i) < heights_i.length (for column-strictness)
            have hk_col_lt : k_j + (mu j - mu i) < (np.paths i).eastStepHeights.length := by
              simp only [k_j]
              have hlen := (np.paths i).length_eq
              simp only [sub_sub_sub_cancel_right] at hlen
              have hx_hi : x ≤ (lam i : ℤ) - (i.val : ℤ) := hx_hi_i
              have hmu_ji : mu i ≤ mu j := hmu j i (Fin.le_of_lt hji_lt)
              have hcont := hcontained i
              have hx_ge : x ≥ (mu j : ℤ) - (j.val : ℤ) := hx_lo_j
              have hnneg : (lam i : ℤ) - (mu i : ℤ) ≥ 0 := by omega
              have hnneg2 : x - ((mu j : ℤ) - (j.val : ℤ)) ≥ 0 := by omega
              have hlt : x - ((mu j : ℤ) - (j.val : ℤ)) + ((mu j : ℤ) - (mu i : ℤ)) < (lam i : ℤ) - (mu i : ℤ) := by omega
              rw [hlen]
              have h1 : ((x - ((mu j : ℤ) - (j.val : ℤ))).toNat : ℤ) = x - ((mu j : ℤ) - (j.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg2
              have h2 : (((lam i : ℤ) - (mu i : ℤ)).toNat : ℤ) = (lam i : ℤ) - (mu i : ℤ) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Show k_i > 0 (path i has taken at least one east step to reach x)
            have hk_i_pos : k_i > 0 := by
              simp only [k_i]
              have hx_ge : x ≥ (mu j : ℤ) - (j.val : ℤ) := hx_lo_j
              have hmu_ji : mu i ≤ mu j := hmu j i (Fin.le_of_lt hji_lt)
              omega
            -- Show k_i - 1 ≥ k_j + (mu_j - mu_i)
            have hk_i_ge : k_i - 1 ≥ k_j + (mu j - mu i) := by
              rw [hk_rel]
              have hji_pos : i.val - j.val ≥ 1 := Nat.sub_pos_of_lt hji_lt
              omega
            -- Apply column-strictness at column mu_j + k_j
            have hcol_eq : mu j + k_j = mu i + (k_j + (mu j - mu i)) := by
              have hmu_ji : mu i ≤ mu j := hmu j i (Fin.le_of_lt hji_lt)
              omega
            have hcolstrict := np.colStrictPaths j i hji_lt k_j hk_j_lt
                (k_j + (mu j - mu i)) hk_col_lt hcol_eq
            -- Apply weakly increasing property of heights_i
            have hk_i_lt : k_i - 1 < (np.paths i).eastStepHeights.length := by
              have hlen : (np.paths i).eastStepHeights.length = lam i - mu i := by
                have h := (np.paths i).length_eq
                simp only [sub_sub_sub_cancel_right] at h
                have hcont := hcontained i
                omega
              rw [hlen]
              simp only [k_i]
              have hx_hi : x ≤ (lam i : ℤ) - (i.val : ℤ) := hx_hi_i
              have hcont := hcontained i
              omega
            have hweakly := List.IsChain.getElem_le_getElem_of_le (np.paths i).weaklyIncreasing
                hk_col_lt hk_i_lt hk_i_ge
            -- Derive: heights_i[k_i-1] > heights_j[k_j]
            have hcontra : (np.paths i).eastStepHeights[k_i - 1] > (np.paths j).eastStepHeights[k_j] :=
              lt_of_lt_of_le hcolstrict hweakly
            -- Get y bounds
            have hy_ge : y ≥ 1 := by
              have hbd := LGV.integerLattice_path_vertices_bounded (pathFn j) idx_j hidx_j
              have h := hbd.2.2.1
              rw [hstart_j] at h
              rw [heq_j_y] at h
              exact h
            have hy_le : y ≤ N := by
              have hbd := LGV.integerLattice_path_vertices_bounded (pathFn j) idx_j hidx_j
              have h := hbd.2.2.2
              rw [hfinish_j] at h
              rw [heq_j_y] at h
              exact h
            have hval_contr : (np.paths i).eastStepHeights[k_i - 1].val >
                              (np.paths j).eastStepHeights[k_j].val := hcontra
            -- Apply y-bound lemmas to derive contradiction
            -- For path j at (x, y): y ≤ heights_j[k_j].val + 1
            -- For path i at (x, y): y ≥ heights_i[k_i-1].val + 1
            --
            -- Set up for buildVertices_y_upper_bound_at_x on path j
            let a_j := (mu j : ℤ) - (j.val : ℤ)
            let c_j := (lam j : ℤ) - (j.val : ℤ)
            have h_ca_j : 0 ≤ c_j - a_j := by
              simp only [c_j, a_j]; have hcont := hcontained j; omega
            have hvertices_j : (pathFn j).vertices = buildVertices a_j c_j N (np.paths j).eastStepHeights := by
              simp only [pathFn, a_j, c_j]
            have hidx_j' : idx_j < (buildVertices a_j c_j N (np.paths j).eastStepHeights).length := by
              rw [← hvertices_j]; exact hidx_j
            have hx_eq_j : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].1 = a_j + k_j := by
              have h1 : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].1 =
                  ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).1 := by
                simp only [hvertices_j, List.get_eq_getElem]
              rw [h1, heq_j_x]
              simp only [k_j, a_j]
              have hnneg : x - ((mu j : ℤ) - (j.val : ℤ)) ≥ 0 := by omega
              have h2 : ((x - ((mu j : ℤ) - (j.val : ℤ))).toNat : ℤ) = x - ((mu j : ℤ) - (j.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Apply buildVertices_y_upper_bound_at_x on path j
            have hy_upper : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].2 ≤
                ((np.paths j).eastStepHeights[k_j]).val + 1 :=
              buildVertices_y_upper_bound_at_x a_j c_j N (np.paths j).eastStepHeights hN_pos
                (np.paths j).length_eq h_ca_j (np.paths j).weaklyIncreasing idx_j hidx_j' k_j hk_j_lt hx_eq_j
            -- Convert to y ≤ heights_j[k_j].val + 1
            have hy_upper' : y ≤ ((np.paths j).eastStepHeights[k_j]).val + 1 := by
              have h1 : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].2 =
                  ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).2 := by
                simp only [hvertices_j, List.get_eq_getElem]
              rw [h1, heq_j_y] at hy_upper
              exact hy_upper
            -- Set up for buildVertices_y_lower_bound_at_x on path i
            let a_i := (mu i : ℤ) - (i.val : ℤ)
            let c_i := (lam i : ℤ) - (i.val : ℤ)
            have h_ca_i : 0 ≤ c_i - a_i := by
              simp only [c_i, a_i]; have hcont := hcontained i; omega
            have hvertices_i : (pathFn i).vertices = buildVertices a_i c_i N (np.paths i).eastStepHeights := by
              simp only [pathFn, a_i, c_i]
            have hidx_i' : idx_i < (buildVertices a_i c_i N (np.paths i).eastStepHeights).length := by
              rw [← hvertices_i]; exact hidx_i
            have hx_eq_i : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].1 = a_i + k_i := by
              have h1 : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].1 =
                  ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).1 := by
                simp only [hvertices_i, List.get_eq_getElem]
              rw [h1, heq_i_x]
              simp only [k_i, a_i]
              have hnneg : x - ((mu i : ℤ) - (i.val : ℤ)) ≥ 0 := by omega
              have h2 : ((x - ((mu i : ℤ) - (i.val : ℤ))).toNat : ℤ) = x - ((mu i : ℤ) - (i.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Need k_i < heights_i.length for the lower bound lemma
            -- Handle the edge case where x = lam_i - i (path i at endpoint)
            have hk_i_strict : k_i < (np.paths i).eastStepHeights.length := by
              have hlen : (np.paths i).eastStepHeights.length = lam i - mu i := by
                have h := (np.paths i).length_eq
                simp only [sub_sub_sub_cancel_right] at h
                have hcont := hcontained i
                omega
              rw [hlen]
              simp only [k_i]
              have hx_hi : x ≤ (lam i : ℤ) - (i.val : ℤ) := hx_hi_i
              have hcont := hcontained i
              have hnneg : (lam i : ℤ) - (mu i : ℤ) ≥ 0 := by omega
              have hnneg2 : x - ((mu i : ℤ) - (i.val : ℤ)) ≥ 0 := by omega
              by_cases hx_eq : x = (lam i : ℤ) - (i.val : ℤ)
              · -- If x = lam_i - i, derive contradiction
                exfalso
                -- At x = lam_i - i, k_i = heights_i.length
                have hk_i_eq : k_i = lam i - mu i := by
                  simp only [k_i, hx_eq]
                  have hnneg3 : (lam i : ℤ) - (i.val : ℤ) - ((mu i : ℤ) - (i.val : ℤ)) ≥ 0 := by omega
                  omega
                have hlen_i : (np.paths i).eastStepHeights.length = lam i - mu i := hlen
                -- Use the upper bound from path j: y ≤ heights_j[k_j] + 1
                have hy_upper_j := hy_upper'
                -- heights_i[k_i - 1] > heights_j[k_j]
                have hcontra_val : (np.paths i).eastStepHeights[k_i - 1].val > (np.paths j).eastStepHeights[k_j].val := hcontra
                -- At x = lam_i - i, k_i - 1 = heights_i.length - 1
                have hk_i_minus_1 : k_i - 1 = (np.paths i).eastStepHeights.length - 1 := by
                  rw [hk_i_eq, hlen_i]
                -- At x = lam_i - i, path i is in its last column
                -- All vertices in this column have y ≥ heights_i[last] + 1
                have hlen_pos : 0 < (np.paths i).eastStepHeights.length := by
                  rw [hlen_i]; omega
                have hy_ge_last : y ≥ ((np.paths i).eastStepHeights[(np.paths i).eastStepHeights.length - 1]).val + 1 := by
                  -- At x = a_i + heights_i.length, path i is in its last column
                  -- The y-coordinate is at least heights_i[last] + 1
                  -- Use buildVertices_y_lower_bound_at_last_column
                  have hx_eq_i_last : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].1 =
                      a_i + (np.paths i).eastStepHeights.length := by
                    have h1 : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].1 =
                        ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).1 := by
                      simp only [hvertices_i, List.get_eq_getElem]
                    rw [h1, heq_i_x, hx_eq]
                    simp only [a_i, hlen_i]
                    omega
                  have hy_lower_last := buildVertices_y_lower_bound_at_last_column a_i c_i N
                    (np.paths i).eastStepHeights hN_pos (np.paths i).length_eq h_ca_i
                    (np.paths i).weaklyIncreasing hlen_pos idx_i hidx_i' hx_eq_i_last
                  have h1 : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].2 =
                      ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).2 := by
                    simp only [hvertices_i, List.get_eq_getElem]
                  rw [h1, heq_i_y] at hy_lower_last
                  exact hy_lower_last
                have hcontra_val' : (np.paths i).eastStepHeights[(np.paths i).eastStepHeights.length - 1].val >
                    (np.paths j).eastStepHeights[k_j].val := by
                  have h : k_i - 1 = (np.paths i).eastStepHeights.length - 1 := hk_i_minus_1
                  simp only [h] at hcontra_val
                  exact hcontra_val
                omega
              · -- x < lam_i - i, so k_i < lam_i - mu_i = heights.length
                have hx_lt : x < (lam i : ℤ) - (i.val : ℤ) := by
                  have h := hx_hi; omega
                have h1 : ((x - ((mu i : ℤ) - (i.val : ℤ))).toNat : ℤ) = x - ((mu i : ℤ) - (i.val : ℤ)) :=
                  Int.toNat_of_nonneg hnneg2
                have h2 : (((lam i : ℤ) - (mu i : ℤ)).toNat : ℤ) = (lam i : ℤ) - (mu i : ℤ) :=
                  Int.toNat_of_nonneg hnneg
                omega
            -- Apply buildVertices_y_lower_bound_at_x
            have hy_lower : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].2 ≥
                ((np.paths i).eastStepHeights[k_i - 1]).val + 1 :=
              buildVertices_y_lower_bound_at_x a_i c_i N (np.paths i).eastStepHeights hN_pos
                (np.paths i).length_eq h_ca_i (np.paths i).weaklyIncreasing idx_i hidx_i' k_i hk_i_strict hk_i_pos hx_eq_i
            -- Convert to y ≥ heights_i[k_i-1].val + 1
            have hy_lower' : y ≥ ((np.paths i).eastStepHeights[k_i - 1]).val + 1 := by
              have h1 : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].2 =
                  ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).2 := by
                simp only [hvertices_i, List.get_eq_getElem]
              rw [h1, heq_i_y] at hy_lower
              exact hy_lower
            -- Combine: heights_i[k_i-1].val + 1 ≤ y ≤ heights_j[k_j].val + 1
            -- So heights_i[k_i-1].val ≤ heights_j[k_j].val
            -- But hval_contr says heights_i[k_i-1].val > heights_j[k_j].val
            omega
      use pt
      refine ⟨?_, ?_⟩
      · -- Show pt ∈ nipatFinset
        rw [LGV.mem_nipatFinset_iff]
        exact hni
      · -- Show pathTupleToNipat pt = np
        -- Need to show the two Nipat structures are equal
        -- This follows from the fact that lgvPathToLatticePath ∘ buildVertices = id
        simp only [pathTupleToNipat]
        congr 1
        funext i
        simp only [pathTupleToLatticePaths, pt, pathFn]
        -- Need to show: lgvPathToLatticePath ... = np.paths i
        -- This follows from lgvPathEastStepYCoords_buildVertices
        apply LatticePath.ext
        simp only [lgvPathToLatticePath]
        have h_ca : 0 ≤ ((lam i : ℤ) - (i.val : ℤ)) - ((mu i : ℤ) - (i.val : ℤ)) := by
          have hcont := hcontained i
          omega
        have heq := lgvPathEastStepYCoords_buildVertices
            ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ))
            (np.paths i).eastStepHeights hN_pos (np.paths i).length_eq h_ca
            (np.paths i).weaklyIncreasing
        exact lgvYCoordsToFinN_map_val_add_one_eq (np.paths i).eastStepHeights heq _
  -- 4. Weight preservation
  · intro pt hpt
    exact pathTupleToNipat_weight lam mu hlam hmu hcontained pt
      ((LGV.mem_nipatFinset_iff LGV.integerLattice_pathFinite pt).mp hpt)

/-- Key lemma: The Jacobi-Trudi matrix determinant equals the sum of nipat weights.

    This is the core connection between the LGV lemma and the Jacobi-Trudi formula.
    The proof follows from:
    1. jacobiTrudiMatrixH entries are h_{λᵢ - μⱼ - i + j} = pathWeightSum from A_j to B_i
    2. By LGV nonpermutable lemma, det(pathWeightMatrix) = sum over nipats
    3. The Nipat type captures exactly the non-intersecting path tuples -/
lemma det_jacobiTrudiMatrixH_eq_nipatSum (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    (jacobiTrudiMatrixH (R := R) lam mu).det =
      ∑ np : Nipat lam mu hlam hmu hcontained, np.weight (R := R) := by
  -- Step 1-2: Reduce to determinant of path weight matrix
  rw [det_jacobiTrudiMatrixH_eq_det_pathWeightMatrix]
  -- Step 3: Apply LGV nonpermutable
  rw [LGV.lgv_nonpermutable (jacobiTrudiArcWeight (N := N) (R := R))
      (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam)
      (jacobiTrudiSourceVertex_xDecreasing mu hmu)
      (jacobiTrudiSourceVertex_yIncreasing mu)
      (jacobiTrudiTargetVertex_xDecreasing lam hlam)
      (jacobiTrudiTargetVertex_yIncreasing lam)]
  -- Step 4: Connect LGV nipats to our Nipat type
  exact lgv_nipatWeightSum_eq_nipatSum lam mu hlam hmu hcontained

/-- First Jacobi-Trudi formula (Theorem thm.sf.jt-h)
    Label: thm.sf.jt-h

    s_{λ/μ} = det((h_{λᵢ - μⱼ - i + j})_{1 ≤ i,j ≤ M})

    The proof uses the Lindström-Gessel-Viennot lemma with appropriate
    source and target vertices in the integer lattice ℤ².

    ## Proof Strategy

    **Step 1: Set up the LGV framework**
    Define source vertices Aᵢ = (μᵢ - i, 1) and target vertices Bⱼ = (λⱼ - j, N) in ℤ².
    The path weight matrix M_{i,j} = ∑_{p : Aᵢ → Bⱼ} w(p) where w(p) is the product
    of x_h for each east-step at height h.

    **Step 2: Identify M with the Jacobi-Trudi matrix**
    By `pathWeightSum_eq_hsymm`, M_{i,j} = h_{λⱼ - μᵢ - j + i} = h_{λⱼ - μᵢ - (j - i)}.
    Note: The textbook uses 1-indexed notation; our Lean formalization uses 0-indexed.
    The matrix entry (i,j) is h_{λᵢ - μⱼ - i + j} in the textbook convention.

    **Step 3: Apply the LGV lemma**
    By `lgv_nonpermutable` (Corollary cor.lgv.kpaths.wt-np), since the source and
    target vertices satisfy the sorting conditions (x-decreasing, y-increasing),
    we have:
      det(M) = ∑_{nipats from 𝐀 to 𝐁} w(nipat)
    where the sum is only over non-intersecting path tuples (nipats).

    **Step 4: Establish the nipat-SSYT bijection**
    By `nipat_ssyt_bijection`, there is a weight-preserving bijection between
    nipats from 𝐀 to 𝐁 and SSYT of skew shape λ/μ:
    - The nipat (p₁, ..., pₖ) maps to the tableau T where row i contains
      the heights of east-steps in path pᵢ (in weakly increasing order).
    - Non-intersection of paths ensures column-strictness of the tableau.
    - The weight w(nipat) = ∏ᵢ w(pᵢ) equals the monomial x^T.

    **Step 5: Conclude**
    det(M) = ∑_{nipats} w(nipat) = ∑_{SSYT T of shape λ/μ} x^T = s_{λ/μ}

    ## Key Lemmas Required

    1. `pathWeightSum_eq_hsymm`: Path weight sums equal h_n (Observation 1)
    2. `nipat_ssyt_bijection`: Bijection between nipats and SSYT (Observation 2)
    3. `lgv_nonpermutable`: LGV lemma for sorted vertices (from LGV2.lean)
    4. Sorting conditions on A and B vertices (follows from partition monotonicity)

    ## References
    - TeX source: AlgebraicCombinatorics/tex/SymmetricFunctions/PieriJacobiTrudi.tex
    - LGV infrastructure: AlgebraicCombinatorics/Determinants/LGV2.lean
-/
lemma jacobiTrudi_h (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    skewSchur (R := R) ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ =
      (jacobiTrudiMatrixH (R := R) lam mu).det := by
  -- The proof combines two key lemmas:
  -- 1. det_jacobiTrudiMatrixH_eq_nipatSum: det(J) = Σ nipat weights
  -- 2. nipatWeightSum_eq_skewSchur: Σ nipat weights = skewSchur
  rw [det_jacobiTrudiMatrixH_eq_nipatSum, nipatWeightSum_eq_skewSchur]


/-- The Schur polynomial for a partition λ equals the skew Schur polynomial for λ/0.
    This follows from the fact that a skew partition λ/0 is just the partition λ,
    so SSYT(λ) and SkewSSYT(λ/0) are in natural bijection. -/
lemma schur_eq_skewSchur_zero (lam : NPartition N) :
    schur (R := R) lam = skewSchur (R := R) ⟨lam, 0, fun _ => Nat.zero_le _⟩ := by
  exact (skewSchur_zero_eq_schur lam.parts lam.weaklyDecreasing).symm

/-- Jacobi-Trudi for non-skew Schur polynomials:
    s_λ = det((h_{λᵢ - i + j})_{1 ≤ i,j ≤ N}) -/
lemma jacobiTrudi_h_nonSkew (lam : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
    schur (R := R) ⟨lam, hlam⟩ =
      (jacobiTrudiMatrixH (R := R) lam (fun _ => 0)).det := by
  -- First, relate schur to skewSchur with inner = 0
  rw [schur_eq_skewSchur_zero]
  -- The zero function is weakly decreasing
  have hmu : ∀ i j : Fin N, i ≤ j → (fun _ : Fin N => 0) j ≤ (fun _ : Fin N => 0) i := by
    intros; rfl
  -- Zero is contained in any partition
  have hcontained : ∀ i, (fun _ : Fin N => 0) i ≤ lam i := fun _ => Nat.zero_le _
  -- Apply the general Jacobi-Trudi formula
  exact jacobiTrudi_h (R := R) lam (fun _ => 0) hlam hmu hcontained


/-- If all entries of a matrix are symmetric polynomials, then the determinant is symmetric.
    This is because rename σ commutes with det, and rename σ fixes each symmetric entry. -/
lemma det_isSymmetric_of_entries_symmetric (M : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) R))
    (h : ∀ i j, (M i j).IsSymmetric) : M.det.IsSymmetric := by
  intro σ
  simp only [Matrix.det_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [Units.smul_def, map_zsmul]
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact h (τ i) i σ

/-- The Jacobi-Trudi matrix (h-version) has symmetric entries. -/
lemma jacobiTrudiMatrixH_entries_isSymmetric (lam mu : Fin N → ℕ) (i j : Fin N) :
    (jacobiTrudiMatrixH (R := R) lam mu i j).IsSymmetric := by
  unfold jacobiTrudiMatrixH
  simp only [Matrix.of_apply]
  exact hsymmExt_isSymmetric _

/-- The determinant of the Jacobi-Trudi matrix (h-version) is symmetric. -/
lemma jacobiTrudiMatrixH_det_isSymmetric (lam mu : Fin N → ℕ) :
    (jacobiTrudiMatrixH (R := R) lam mu).det.IsSymmetric := by
  apply det_isSymmetric_of_entries_symmetric
  exact jacobiTrudiMatrixH_entries_isSymmetric lam mu

/-- **Skew Schur polynomials are symmetric (via Jacobi-Trudi).**

    This provides a sorry-free proof of symmetry using the Jacobi-Trudi formula,
    complementing the Bender-Knuth approach in SchurBasics.lean.

    The proof works by:
    1. Using `jacobiTrudi_h` to express skewSchur as det(jacobiTrudiMatrixH)
    2. Showing each entry h_{λᵢ - μⱼ - i + j} is symmetric (via `hsymmExt_isSymmetric`)
    3. Concluding the determinant is symmetric (via `det_isSymmetric_of_entries_symmetric`)

    Theorem \ref{thm.sf.skew-schur-symm} in the source. -/
lemma skewSchur_isSymmetric_jacobiTrudi (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    (skewSchur (R := R) ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩).IsSymmetric := by
  rw [jacobiTrudi_h lam mu hlam hmu hcontained]
  exact jacobiTrudiMatrixH_det_isSymmetric lam mu

/-- **Schur polynomials are symmetric (via Jacobi-Trudi).**

    This is a corollary of `skewSchur_isSymmetric_jacobiTrudi` with μ = 0.

    Theorem \ref{thm.sf.schur-symm}(a) in the source. -/
lemma schur_isSymmetric_jacobiTrudi (lam : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
    (schur (R := R) ⟨lam, hlam⟩).IsSymmetric := by
  rw [schur_eq_skewSchur_zero]
  have hmu : ∀ i j : Fin N, i ≤ j → (fun _ : Fin N => 0) j ≤ (fun _ : Fin N => 0) i := by
    intros; rfl
  have hcontained : ∀ i, (fun _ : Fin N => 0) i ≤ lam i := fun _ => Nat.zero_le _
  exact skewSchur_isSymmetric_jacobiTrudi lam (fun _ => 0) hlam hmu hcontained

end SymmetricFunctions
end


/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_ext
  {N : ℕ}
  {lam mu : SymmetricFunctions.NPartition N}
-- given
  (h : lam.parts = mu.parts) :
-- imply
  lam = mu := by
-- proof
  apply SymmetricFunctions.NPartition.ext h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_le_def
  {N : ℕ}
-- given
  (mu lam : SymmetricFunctions.NPartition N) :
-- imply
  mu ≤ lam ↔ ∀ i, mu.parts i ≤ lam.parts i := by
-- proof
  apply SymmetricFunctions.NPartition.le_def mu lam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_zero_isTranspose
  {N : ℕ} :
-- imply
  IsTranspose (fun _ : Fin N => 0) (fun _ : Fin N => 0) := by
-- proof
  apply SymmetricFunctions.NPartition.zero_isTranspose

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_box_equiv
  {N M : ℕ}
  {lam : Fin N → ℕ}
  {lamt : Fin M → ℕ}
-- given
  (hlam_mono : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
  (hlamt_mono : ∀ i j : Fin M, i ≤ j → lamt j ≤ lamt i)
  (htranspose : IsTranspose lam lamt)
  (i : Fin N)
  (j : Fin M) :
-- imply
  j.val + 1 ≤ lam i ↔ i.val + 1 ≤ lamt j := by
-- proof
  apply SymmetricFunctions.NPartition.IsTranspose.box_equiv hlam_mono hlamt_mono htranspose i j

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_sum_eq
  {N M : ℕ}
  {lam : Fin N → ℕ}
  {lamt : Fin M → ℕ}
-- given
  (hlam_mono : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
  (hlamt_mono : ∀ i j : Fin M, i ≤ j → lamt j ≤ lamt i)
  (htranspose : IsTranspose lam lamt) :
-- imply
  ∑ i : Fin N, lam i = ∑ j : Fin M, lamt j := by
-- proof
  apply SymmetricFunctions.NPartition.IsTranspose.sum_eq hlam_mono hlamt_mono htranspose

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_rowPartition_size
-- given
  (N : ℕ)
  (hN : 0 < N)
  (n : ℕ) :
-- imply
  (rowPartition N n hN).size = n := by
-- proof
  apply SymmetricFunctions.NPartition.rowPartition_size N n hN

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_rowPartition_parts_zero
-- given
  (N : ℕ)
  (hN : 0 < N)
  (n : ℕ) :
-- imply
  (rowPartition N n hN).parts ⟨0, hN⟩ = n := by
-- proof
  apply SymmetricFunctions.NPartition.rowPartition_parts_zero N n hN

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_rowPartition_parts_pos
-- given
  (N : ℕ)
  (i : Fin N)
  (hN : 0 < N)
  (hi : 0 < i.val)
  (n : ℕ) :
-- imply
  (rowPartition N n hN).parts i = 0 := by
-- proof
  apply SymmetricFunctions.NPartition.rowPartition_parts_pos N n hN i hi

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_colPartition_size
-- given
  (N n : ℕ)
  (hn : n ≤ N) :
-- imply
  (colPartition N n hn).size = n := by
-- proof
  apply SymmetricFunctions.NPartition.colPartition_size N n hn

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_colPartition_parts_lt
-- given
  (N n : ℕ)
  (i : Fin N)
  (hn : n ≤ N)
  (hi : i.val < n) :
-- imply
  (colPartition N n hn).parts i = 1 := by
-- proof
  apply SymmetricFunctions.NPartition.colPartition_parts_lt N n hn i hi

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_colPartition_parts_ge
-- given
  (N n : ℕ)
  (i : Fin N)
  (hn : n ≤ N)
  (hi : n ≤ i.val) :
-- imply
  (colPartition N n hn).parts i = 0 := by
-- proof
  apply SymmetricFunctions.NPartition.colPartition_parts_ge N n hn i hi

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_ofShared_toShared
  {N : ℕ}
-- given
  (μ : SymmetricFunctions.NPartition N) :
-- imply
  SymmetricFunctions.NPartition.ofShared (SymmetricFunctions.NPartition.toShared μ) = μ := by
-- proof
  apply SymmetricFunctions.NPartition.ofShared_toShared μ

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_toShared_ofShared
  {N : ℕ}
-- given
  (μ : _root_.NPartition N) :
-- imply
  SymmetricFunctions.NPartition.toShared (SymmetricFunctions.NPartition.ofShared μ) = μ := by
-- proof
  apply SymmetricFunctions.NPartition.toShared_ofShared μ

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_toShared_parts
  {N : ℕ}
-- given
  (μ : SymmetricFunctions.NPartition N) :
-- imply
  (SymmetricFunctions.NPartition.toShared μ).parts = μ.parts := by
-- proof
  apply SymmetricFunctions.NPartition.toShared_parts μ

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_ofShared_parts
  {N : ℕ}
-- given
  (μ : _root_.NPartition N) :
-- imply
  (SymmetricFunctions.NPartition.ofShared μ).parts = μ.parts := by
-- proof
  apply SymmetricFunctions.NPartition.ofShared_parts μ

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_toShared_size
  {N : ℕ}
-- given
  (μ : SymmetricFunctions.NPartition N) :
-- imply
  (SymmetricFunctions.NPartition.toShared μ).size = μ.size := by
-- proof
  apply SymmetricFunctions.NPartition.toShared_size μ

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_ofShared_size
  {N : ℕ}
-- given
  (μ : _root_.NPartition N) :
-- imply
  (SymmetricFunctions.NPartition.ofShared μ).size = μ.size := by
-- proof
  apply SymmetricFunctions.NPartition.ofShared_size μ

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_toShared_zero
  {N : ℕ} :
-- imply
  SymmetricFunctions.NPartition.toShared (0 : SymmetricFunctions.NPartition N) = 0 := by
-- proof
  apply SymmetricFunctions.NPartition.toShared_zero

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_ofShared_zero
  {N : ℕ} :
-- imply
  SymmetricFunctions.NPartition.ofShared (0 : _root_.NPartition N) = 0 := by
-- proof
  apply SymmetricFunctions.NPartition.ofShared_zero

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_toShared_le_iff
  {N : ℕ}
-- given
  (μ ν : SymmetricFunctions.NPartition N) :
-- imply
  SymmetricFunctions.NPartition.toShared μ ≤ SymmetricFunctions.NPartition.toShared ν ↔ μ ≤ ν := by
-- proof
  apply SymmetricFunctions.NPartition.toShared_le_iff μ ν

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_ofShared_le_iff
  {N : ℕ}
-- given
  (μ ν : _root_.NPartition N) :
-- imply
  SymmetricFunctions.NPartition.ofShared μ ≤ SymmetricFunctions.NPartition.ofShared ν ↔ μ ≤ ν := by
-- proof
  apply SymmetricFunctions.NPartition.ofShared_le_iff μ ν

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_transpose_toShared_eq
  {N : ℕ}
-- given
  (hN : 0 < N)
  (lam : SymmetricFunctions.NPartition N) :
-- imply
  (lam.transpose hN).toShared = (lam.toShared).transpose hN := by
-- proof
  apply SymmetricFunctions.NPartition.transpose_toShared_eq lam hN

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_ofShared_transpose_eq
  {N : ℕ}
-- given
  (hN : 0 < N)
  (lam : _root_.NPartition N) :
-- imply
  SymmetricFunctions.NPartition.ofShared (lam.transpose hN) = (SymmetricFunctions.NPartition.ofShared lam).transpose hN := by
-- proof
  apply SymmetricFunctions.NPartition.ofShared_transpose_eq lam hN

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_equivShared_transpose
  {N : ℕ}
-- given
  (hN : 0 < N)
  (lam : SymmetricFunctions.NPartition N) :
-- imply
  SymmetricFunctions.NPartition.equivShared (lam.transpose hN) = (SymmetricFunctions.NPartition.equivShared lam).transpose hN := by
-- proof
  apply SymmetricFunctions.NPartition.equivShared_transpose lam hN

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_sym_monomial_eq_weaklyIncreasing_prod
  [CommRing R]
  {N : ℕ}
-- given
  (n : ℕ)
  (s : Sym (Fin N) n) :
-- imply
  (s.1.map (MvPolynomial.X (R := R))).prod = ∏ j : Fin n, MvPolynomial.X ((symToWeaklyIncreasing n s).val j) := by
-- proof
  apply SymmetricFunctions.sym_monomial_eq_weaklyIncreasing_prod n s

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_weaklyIncreasingToSym_symToWeaklyIncreasing
  {N : ℕ}
-- given
  (n : ℕ)
  (s : Sym (Fin N) n) :
-- imply
  weaklyIncreasingToSym n (symToWeaklyIncreasing n s).val = s := by
-- proof
  apply SymmetricFunctions.weaklyIncreasingToSym_symToWeaklyIncreasing n s

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_horizontalStrip_iff_entries
  {N : ℕ}
-- given
  (s : SkewPartition N) :
-- imply
  s.isHorizontalStrip ↔ ∀ i : Fin N, ∀ hi : i.val + 1 < N, s.outer.parts i ≥ s.inner.parts i ∧ s.inner.parts i ≥ s.outer.parts ⟨i.val + 1, hi⟩ := by
-- proof
  apply SymmetricFunctions.SkewPartition.horizontalStrip_iff_entries s

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_verticalStrip_iff_entries
  {N : ℕ}
-- given
  (s : SkewPartition N) :
-- imply
  s.isVerticalStrip ↔ ∀ i : Fin N, s.inner.parts i ≤ s.outer.parts i ∧ s.outer.parts i ≤ s.inner.parts i + 1 := by
-- proof
  apply SymmetricFunctions.SkewPartition.verticalStrip_iff_entries s

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_size_eq
  {N : ℕ}
  {s : SkewPartition N}
  {n : ℕ}
-- given
  (h : s.isHorizontalNStrip n) :
-- imply
  s.size = n := by
-- proof
  apply SymmetricFunctions.SkewPartition.isHorizontalNStrip.size_eq h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_isVerticalNStrip_size_eq
  {N : ℕ}
  {s : SkewPartition N}
  {n : ℕ}
-- given
  (h : s.isVerticalNStrip n) :
-- imply
  s.size = n := by
-- proof
  apply SymmetricFunctions.SkewPartition.isVerticalNStrip.size_eq h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_isHorizontalStrip
  {N : ℕ}
  {s : SkewPartition N}
  {n : ℕ}
-- given
  (h : s.isHorizontalNStrip n) :
-- imply
  s.isHorizontalStrip := by
-- proof
  apply SymmetricFunctions.SkewPartition.isHorizontalNStrip.isHorizontalStrip h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_isVerticalStrip
  {N : ℕ}
  {s : SkewPartition N}
  {n : ℕ}
-- given
  (h : s.isVerticalNStrip n) :
-- imply
  s.isVerticalStrip := by
-- proof
  apply SymmetricFunctions.SkewPartition.isVerticalNStrip.isVerticalStrip h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_empty_isHorizontalNStrip
  {N : ℕ}
-- given
  (lam : SymmetricFunctions.NPartition N) :
-- imply
  (⟨lam, lam, fun _ => le_refl _⟩ : SkewPartition N).isHorizontalNStrip 0 := by
-- proof
  apply SymmetricFunctions.SkewPartition.empty_isHorizontalNStrip lam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_empty_isVerticalNStrip
  {N : ℕ}
-- given
  (lam : SymmetricFunctions.NPartition N) :
-- imply
  (⟨lam, lam, fun _ => le_refl _⟩ : SkewPartition N).isVerticalNStrip 0 := by
-- proof
  apply SymmetricFunctions.SkewPartition.empty_isVerticalNStrip lam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_eq_of_entries_eq
  {N : ℕ}
  {s : SkewPartition N}
  {T1 T2 : SkewSSYT s}
-- given
  (h : T1.entries = T2.entries) :
-- imply
  T1 = T2 := by
-- proof
  apply SymmetricFunctions.SkewSSYT.eq_of_entries_eq h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_SSYT_eq_of_entries_eq
  {N : ℕ}
  {lam : SymmetricFunctions.NPartition N}
  {T1 T2 : SSYT lam}
-- given
  (h : T1.entries = T2.entries) :
-- imply
  T1 = T2 := by
-- proof
  apply SymmetricFunctions.SSYT.eq_of_entries_eq h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_colStrict_nonadjacent
  {N : ℕ}
  {s : SkewPartition N}
-- given
  (i j : Fin N)
  (k : Fin (s.outer.parts i - s.inner.parts i))
  (k' : Fin (s.outer.parts j - s.inner.parts j))
  (hij : i < j)
  (hcol_eq : s.inner.parts i + k.val = s.inner.parts j + k'.val)
  (T : SkewSSYT s) :
-- imply
  T.entries i k < T.entries j k' := by
-- proof
  apply SymmetricFunctions.SkewSSYT.colStrict_nonadjacent T i j hij k k' hcol_eq

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_entries_isSSYTFillingNonSkew
  {N : ℕ}
  {lam : SymmetricFunctions.NPartition N}
-- given
  (T : SSYT lam) :
-- imply
  isSSYTFillingNonSkew lam T.entries := by
-- proof
  apply SymmetricFunctions.SSYT.entries_isSSYTFillingNonSkew T

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_entries_mem_ssytFillingFinsetNonSkew
  {N : ℕ}
  {lam : SymmetricFunctions.NPartition N}
-- given
  (T : SSYT lam) :
-- imply
  T.entries ∈ ssytFillingFinsetNonSkew lam := by
-- proof
  apply SymmetricFunctions.SSYT.entries_mem_ssytFillingFinsetNonSkew T

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_ssytFinset_mem
  {N : ℕ}
-- given
  (lam : SymmetricFunctions.NPartition N)
  (T : SSYT lam) :
-- imply
  T ∈ ssytFinset lam := by
-- proof
  apply SymmetricFunctions.ssytFinset_mem lam T

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_toFilling_isSSYTFilling
  {N : ℕ}
  {s : SkewPartition N}
-- given
  (T : SkewSSYT s) :
-- imply
  isSSYTFilling s T.toFilling := by
-- proof
  apply SymmetricFunctions.SkewSSYT.toFilling_isSSYTFilling T

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_entries_mem_ssytFillingFinset
  {N : ℕ}
  {s : SkewPartition N}
-- given
  (T : SkewSSYT s) :
-- imply
  T.entries ∈ ssytFillingFinset s := by
-- proof
  apply SymmetricFunctions.SkewSSYT.entries_mem_ssytFillingFinset T

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_skewSSYTFinset_mem
  {N : ℕ}
-- given
  (s : SkewPartition N)
  (T : SkewSSYT s) :
-- imply
  T ∈ skewSSYTFinset s := by
-- proof
  apply SymmetricFunctions.skewSSYTFinset_mem s T

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_eq_unique
  {N : ℕ}
-- given
  (T : SSYT (0 : SymmetricFunctions.NPartition N)) :
-- imply
  T = SSYT.unique := by
-- proof
  apply SymmetricFunctions.SSYT.eq_unique T

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_toMonomial_unique
  [CommRing R]
  {N : ℕ} :
-- imply
  (SSYT.unique (N := N)).toMonomial (R := R) = 1 := by
-- proof
  apply SymmetricFunctions.SSYT.toMonomial_unique

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_ssytFinset_zero
  {N : ℕ} :
-- imply
  ssytFinset (0 : SymmetricFunctions.NPartition N) = {SSYT.unique} := by
-- proof
  apply SymmetricFunctions.ssytFinset_zero

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_schur_zero
  [CommRing R]
  {N : ℕ} :
-- imply
  schur (0 : SymmetricFunctions.NPartition N) = (1 : MvPolynomial (Fin N) R) := by
-- proof
  apply SymmetricFunctions.schur_zero

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_ssytToSkewSSYT_skewSSYTToSSYT
  {N : ℕ}
-- given
  (lam : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
  (T : SSYT ⟨lam, hlam⟩) :
-- imply
  skewSSYTToSSYT lam hlam (ssytToSkewSSYT lam hlam T) = T := by
-- proof
  apply SymmetricFunctions.ssytToSkewSSYT_skewSSYTToSSYT lam hlam T

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_skewSSYTToSSYT_ssytToSkewSSYT
  {N : ℕ}
-- given
  (lam : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
  (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨fun _ => 0, fun _ _ _ => le_refl 0⟩, fun _ => Nat.zero_le _⟩) :
-- imply
  ssytToSkewSSYT lam hlam (skewSSYTToSSYT lam hlam T) = T := by
-- proof
  apply SymmetricFunctions.skewSSYTToSSYT_ssytToSkewSSYT lam hlam T

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_ssytToSkewSSYT_toMonomial
  [CommRing R]
  {N : ℕ}
-- given
  (lam : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
  (T : SSYT ⟨lam, hlam⟩) :
-- imply
  (ssytToSkewSSYT lam hlam T).toMonomial = T.toMonomial (R := R) := by
-- proof
  apply SymmetricFunctions.ssytToSkewSSYT_toMonomial lam hlam T

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_skewSchur_zero_eq_schur
  [CommRing R]
  {N : ℕ}
-- given
  (lam : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
-- imply
  skewSchur (R := R) ⟨⟨lam, hlam⟩, ⟨fun _ => 0, fun _ _ _ => le_refl 0⟩, fun _ => Nat.zero_le _⟩ = schur (R := R) ⟨lam, hlam⟩ := by
-- proof
  apply SymmetricFunctions.skewSchur_zero_eq_schur lam hlam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_horizontalNStripPartitions_contained
  {N : ℕ}
-- given
  (mu : SymmetricFunctions.NPartition N)
  (n : ℕ)
  (lam : SymmetricFunctions.NPartition N)
  (hlam : lam ∈ horizontalNStripPartitions mu n) :
-- imply
  mu ≤ lam := by
-- proof
  apply SymmetricFunctions.horizontalNStripPartitions_contained mu n lam hlam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_horizontalNStripPartitions_isHorizontalStrip
  {N : ℕ}
-- given
  (mu : SymmetricFunctions.NPartition N)
  (n : ℕ)
  (lam : SymmetricFunctions.NPartition N)
  (hlam : lam ∈ horizontalNStripPartitions mu n) :
-- imply
  (⟨lam, mu, horizontalNStripPartitions_contained mu n lam hlam⟩ : SkewPartition N).isHorizontalStrip := by
-- proof
  apply SymmetricFunctions.horizontalNStripPartitions_isHorizontalStrip mu n lam hlam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_horizontalNStripPartitions_size
  {N : ℕ}
-- given
  (mu : SymmetricFunctions.NPartition N)
  (n : ℕ)
  (lam : SymmetricFunctions.NPartition N)
  (hlam : lam ∈ horizontalNStripPartitions mu n) :
-- imply
  lam.size - mu.size = n := by
-- proof
  apply SymmetricFunctions.horizontalNStripPartitions_size mu n lam hlam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_horizontalNStripPartitions_isHorizontalNStrip'
  {N : ℕ}
-- given
  (mu : SymmetricFunctions.NPartition N)
  (n : ℕ)
  (lam : SymmetricFunctions.NPartition N)
  (hlam : lam ∈ horizontalNStripPartitions mu n) :
-- imply
  (⟨lam, mu, horizontalNStripPartitions_contained mu n lam hlam⟩ : SkewPartition N).isHorizontalNStrip n := by
-- proof
  apply SymmetricFunctions.horizontalNStripPartitions_isHorizontalNStrip' mu n lam hlam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_verticalNStripPartitions_contained
  {N : ℕ}
-- given
  (mu : SymmetricFunctions.NPartition N)
  (n : ℕ)
  (lam : SymmetricFunctions.NPartition N)
  (hlam : lam ∈ verticalNStripPartitions mu n) :
-- imply
  mu ≤ lam := by
-- proof
  apply SymmetricFunctions.verticalNStripPartitions_contained mu n lam hlam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_verticalNStripPartitions_isVerticalStrip
  {N : ℕ}
-- given
  (mu : SymmetricFunctions.NPartition N)
  (n : ℕ)
  (lam : SymmetricFunctions.NPartition N)
  (hlam : lam ∈ verticalNStripPartitions mu n) :
-- imply
  (⟨lam, mu, verticalNStripPartitions_contained mu n lam hlam⟩ : SkewPartition N).isVerticalStrip := by
-- proof
  apply SymmetricFunctions.verticalNStripPartitions_isVerticalStrip mu n lam hlam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_verticalNStripPartitions_size
  {N : ℕ}
-- given
  (mu : SymmetricFunctions.NPartition N)
  (n : ℕ)
  (lam : SymmetricFunctions.NPartition N)
  (hlam : lam ∈ verticalNStripPartitions mu n) :
-- imply
  lam.size - mu.size = n := by
-- proof
  apply SymmetricFunctions.verticalNStripPartitions_size mu n lam hlam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_verticalNStripPartitions_isVerticalNStrip'
  {N : ℕ}
-- given
  (mu : SymmetricFunctions.NPartition N)
  (n : ℕ)
  (lam : SymmetricFunctions.NPartition N)
  (hlam : lam ∈ verticalNStripPartitions mu n) :
-- imply
  (⟨lam, mu, verticalNStripPartitions_contained mu n lam hlam⟩ : SkewPartition N).isVerticalNStrip n := by
-- proof
  apply SymmetricFunctions.verticalNStripPartitions_isVerticalNStrip' mu n lam hlam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_mem_horizontalNStripPartitions_iff
  {N : ℕ}
-- given
  (mu : SymmetricFunctions.NPartition N)
  (n : ℕ)
  (lam : SymmetricFunctions.NPartition N) :
-- imply
  lam ∈ horizontalNStripPartitions mu n ↔ (∀ i, mu.parts i ≤ lam.parts i) ∧ isHorizontalStripFun lam.parts mu.parts ∧ hasSizeDiff mu.parts lam.parts n ∧ (∀ i, lam.parts i ≤ horizontalStripUpperBound mu n i) := by
-- proof
  apply SymmetricFunctions.mem_horizontalNStripPartitions_iff mu n lam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_mem_verticalNStripPartitions_iff
  {N : ℕ}
-- given
  (mu : SymmetricFunctions.NPartition N)
  (n : ℕ)
  (lam : SymmetricFunctions.NPartition N) :
-- imply
  lam ∈ verticalNStripPartitions mu n ↔ (∀ i, mu.parts i ≤ lam.parts i) ∧ isVerticalStripFun lam.parts mu.parts ∧ hasSizeDiff mu.parts lam.parts n := by
-- proof
  apply SymmetricFunctions.mem_verticalNStripPartitions_iff mu n lam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_hasSizeDiff_of_isHorizontalNStrip
  {N : ℕ}
-- given
  (mu : SymmetricFunctions.NPartition N)
  (n : ℕ)
  (lam : SymmetricFunctions.NPartition N)
  (hcontained : mu ≤ lam)
  (hstrip : (⟨lam, mu, hcontained⟩ : SkewPartition N).isHorizontalNStrip n) :
-- imply
  hasSizeDiff mu.parts lam.parts n := by
-- proof
  apply SymmetricFunctions.hasSizeDiff_of_isHorizontalNStrip mu n lam hcontained hstrip

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_hasSizeDiff_of_isVerticalNStrip
  {N : ℕ}
-- given
  (mu : SymmetricFunctions.NPartition N)
  (n : ℕ)
  (lam : SymmetricFunctions.NPartition N)
  (hcontained : mu ≤ lam)
  (hstrip : (⟨lam, mu, hcontained⟩ : SkewPartition N).isVerticalNStrip n) :
-- imply
  hasSizeDiff mu.parts lam.parts n := by
-- proof
  apply SymmetricFunctions.hasSizeDiff_of_isVerticalNStrip mu n lam hcontained hstrip

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_mem_horizontalNStripPartitions_of_isHorizontalNStrip
  {N : ℕ}
-- given
  (mu : SymmetricFunctions.NPartition N)
  (n : ℕ)
  (lam : SymmetricFunctions.NPartition N)
  (hcontained : mu ≤ lam)
  (hstrip : (⟨lam, mu, hcontained⟩ : SkewPartition N).isHorizontalNStrip n)
  (hbound : ∀ i, lam.parts i ≤ horizontalStripUpperBound mu n i) :
-- imply
  lam ∈ horizontalNStripPartitions mu n := by
-- proof
  apply SymmetricFunctions.mem_horizontalNStripPartitions_of_isHorizontalNStrip mu n lam hcontained hstrip hbound

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_mem_verticalNStripPartitions_of_isVerticalNStrip
  {N : ℕ}
-- given
  (mu : SymmetricFunctions.NPartition N)
  (n : ℕ)
  (lam : SymmetricFunctions.NPartition N)
  (hcontained : mu ≤ lam)
  (hstrip : (⟨lam, mu, hcontained⟩ : SkewPartition N).isVerticalNStrip n) :
-- imply
  lam ∈ verticalNStripPartitions mu n := by
-- proof
  apply SymmetricFunctions.mem_verticalNStripPartitions_of_isVerticalNStrip mu n lam hcontained hstrip

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_rowPartitionFun_zero
-- given
  (N : ℕ)
  (hN : 0 < N)
  (n : ℕ) :
-- imply
  rowPartitionFun N n hN ⟨0, hN⟩ = n := by
-- proof
  apply SymmetricFunctions.rowPartitionFun_zero N n hN

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_rowPartitionFun_pos
-- given
  (N : ℕ)
  (i : Fin N)
  (hN : 0 < N)
  (hi : 0 < i.val)
  (n : ℕ) :
-- imply
  rowPartitionFun N n hN i = 0 := by
-- proof
  apply SymmetricFunctions.rowPartitionFun_pos N n hN i hi

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_colPartitionFun_lt
-- given
  (N n : ℕ)
  (i : Fin N)
  (hn : n ≤ N)
  (hi : i.val < n) :
-- imply
  colPartitionFun N n hn i = 1 := by
-- proof
  apply SymmetricFunctions.colPartitionFun_lt N n hn i hi

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_colPartitionFun_ge
-- given
  (N n : ℕ)
  (i : Fin N)
  (hn : n ≤ N)
  (hi : n ≤ i.val) :
-- imply
  colPartitionFun N n hn i = 0 := by
-- proof
  apply SymmetricFunctions.colPartitionFun_ge N n hn i hi

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_rowPartitionFun_isNPartition
-- given
  (N : ℕ)
  (hN : 0 < N)
  (n : ℕ) :
-- imply
  _root_.IsNPartition (rowPartitionFun N n hN) := by
-- proof
  apply SymmetricFunctions.rowPartitionFun_isNPartition N n hN

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_colPartitionFun_isNPartition
-- given
  (N n : ℕ)
  (hn : n ≤ N) :
-- imply
  _root_.IsNPartition (colPartitionFun N n hn) := by
-- proof
  apply SymmetricFunctions.colPartitionFun_isNPartition N n hn

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_isHorizontalStrip_iff_isHorizontalStripFun
  {N : ℕ}
-- given
  (s : SkewPartition N) :
-- imply
  s.isHorizontalStrip ↔ isHorizontalStripFun s.outer.parts s.inner.parts := by
-- proof
  apply SymmetricFunctions.SkewPartition.isHorizontalStrip_iff_isHorizontalStripFun s

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_isVerticalStrip_iff_isVerticalStripFun
  {N : ℕ}
-- given
  (s : SkewPartition N) :
-- imply
  s.isVerticalStrip ↔ isVerticalStripFun s.outer.parts s.inner.parts := by
-- proof
  apply SymmetricFunctions.SkewPartition.isVerticalStrip_iff_isVerticalStripFun s

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_contentColGeq_zero_of_allEntriesZero
  {N : ℕ}
  {lam mu : Fin N → ℕ}
-- given
  (T : AlgebraicCombinatorics.Tableau lam mu)
  (k : Fin N)
  (hZero : allEntriesZero T)
  (hk : 0 < k.val)
  (j : ℕ) :
-- imply
  AlgebraicCombinatorics.contentColGeq T j k = 0 := by
-- proof
  apply SymmetricFunctions.contentColGeq_zero_of_allEntriesZero T hZero j k hk

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_allEntriesZero_implies_isYamanouchi_rowPartition
  {N : ℕ}
  {lam mu : Fin N → ℕ}
-- given
  (T : AlgebraicCombinatorics.Tableau lam mu)
  (hN : 0 < N)
  (hSS : AlgebraicCombinatorics.IsSemistandard T)
  (hZero : allEntriesZero T) :
-- imply
  ∀ n : ℕ, AlgebraicCombinatorics.IsYamanouchi (rowPartitionFun N n hN) T := by
-- proof
  apply SymmetricFunctions.allEntriesZero_implies_isYamanouchi_rowPartition hN T hSS hZero

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_rowSSYTToSym_symToRowSSYT
  {N : ℕ}
-- given
  (hN : 0 < N)
  (n : ℕ)
  (s : Sym (Fin N) n) :
-- imply
  rowSSYTToSym hN n (symToRowSSYT hN n s) = s := by
-- proof
  apply SymmetricFunctions.rowSSYTToSym_symToRowSSYT hN n s

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_symToRowSSYT_toMonomial
  [CommRing R]
  {N : ℕ}
-- given
  (hN : 0 < N)
  (n : ℕ)
  (s : Sym (Fin N) n) :
-- imply
  (symToRowSSYT hN n s).toMonomial (R := R) = (s.1.map MvPolynomial.X).prod := by
-- proof
  apply SymmetricFunctions.symToRowSSYT_toMonomial hN n s

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_hsymm_eq_schur_rowPartition
  [CommRing R]
  {N : ℕ}
-- given
  (hN : 0 < N)
  (n : ℕ) :
-- imply
  hsymm (Fin N) R n = schur (SymmetricFunctions.NPartition.rowPartition N n hN) := by
-- proof
  apply SymmetricFunctions.hsymm_eq_schur_rowPartition hN n

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_colSSYTEntry_succ_lt
  {N : ℕ}
-- given
  (n k : ℕ)
  (hn : n ≤ N)
  (hk : k < n)
  (hk1 : k + 1 < n)
  (T : SSYT (SymmetricFunctions.NPartition.colPartition N n hn)) :
-- imply
  colSSYTEntry n hn T k hk < colSSYTEntry n hn T (k + 1) hk1 := by
-- proof
  apply SymmetricFunctions.colSSYTEntry_succ_lt n hn T k hk hk1

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_colSSYTEntry_strictMono
  {N : ℕ}
-- given
  (n k₁ k₂ : ℕ)
  (hn : n ≤ N)
  (hk₁ : k₁ < n)
  (hk₂ : k₂ < n)
  (hlt : k₁ < k₂)
  (T : SSYT (SymmetricFunctions.NPartition.colPartition N n hn)) :
-- imply
  colSSYTEntry n hn T k₁ hk₁ < colSSYTEntry n hn T k₂ hk₂ := by
-- proof
  apply SymmetricFunctions.colSSYTEntry_strictMono n hn T k₁ k₂ hk₁ hk₂ hlt

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_colSSYTToFinset_card
  {N : ℕ}
-- given
  (n : ℕ)
  (hn : n ≤ N)
  (T : SSYT (SymmetricFunctions.NPartition.colPartition N n hn)) :
-- imply
  (colSSYTToFinset n hn T).card = n := by
-- proof
  apply SymmetricFunctions.colSSYTToFinset_card n hn T

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_colSSYTToFinset_sort_eq
  {N : ℕ}
-- given
  (n : ℕ)
  (hn : n ≤ N)
  (T : SSYT (SymmetricFunctions.NPartition.colPartition N n hn)) :
-- imply
  (colSSYTToFinset n hn T).sort (· ≤ ·) = List.ofFn (fun k : Fin n => colSSYTEntry n hn T k.val k.isLt) := by
-- proof
  apply SymmetricFunctions.colSSYTToFinset_sort_eq n hn T

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_finsetToColSSYT_toMonomial
  [CommRing R]
  {N : ℕ}
-- given
  (n : ℕ)
  (s : Finset (Fin N))
  (hn : n ≤ N)
  (hs : s.card = n) :
-- imply
  (finsetToColSSYT n hn s hs).toMonomial (R := R) = ∏ i ∈ s, MvPolynomial.X i := by
-- proof
  apply SymmetricFunctions.finsetToColSSYT_toMonomial n hn s hs

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_esymm_eq_schur_colPartition
  [CommRing R]
  {N : ℕ}
-- given
  (n : ℕ)
  (hn : n ≤ N) :
-- imply
  esymm (Fin N) R n = schur (SymmetricFunctions.NPartition.colPartition N n hn) := by
-- proof
  apply SymmetricFunctions.esymm_eq_schur_colPartition n hn

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_hsymmExt_isSymmetric
  [CommRing R]
  {N : ℕ}
-- given
  (n : ℤ) :
-- imply
  (hsymmExt (N := N) (R := R) n).IsSymmetric := by
-- proof
  apply SymmetricFunctions.hsymmExt_isSymmetric n

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_jacobiTrudiSourceX_antitone
  {N : ℕ}
-- given
  (mu : Fin N → ℕ)
  (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i) :
-- imply
  ∀ i j : Fin N, i ≤ j → jacobiTrudiSourceX mu j ≤ jacobiTrudiSourceX mu i := by
-- proof
  apply SymmetricFunctions.jacobiTrudiSourceX_antitone mu hmu

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_jacobiTrudiTargetX_antitone
  {N : ℕ}
-- given
  (lam : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
-- imply
  ∀ i j : Fin N, i ≤ j → jacobiTrudiTargetX lam j ≤ jacobiTrudiTargetX lam i := by
-- proof
  apply SymmetricFunctions.jacobiTrudiTargetX_antitone lam hlam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_jacobiTrudiPathLength
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ)
  (i j : Fin N) :
-- imply
  jacobiTrudiTargetX lam j - jacobiTrudiSourceX mu i = (lam j : ℤ) - (mu i : ℤ) - (j.val : ℤ) + (i.val : ℤ) := by
-- proof
  apply SymmetricFunctions.jacobiTrudiPathLength lam mu i j

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_jacobiTrudiMatrixH_eq_pathLength
  [CommRing R]
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ)
  (i j : Fin N) :
-- imply
  jacobiTrudiMatrixH (R := R) lam mu i j = hsymmExt (N := N) (R := R) (jacobiTrudiTargetX lam i - jacobiTrudiSourceX mu j) := by
-- proof
  apply SymmetricFunctions.jacobiTrudiMatrixH_eq_pathLength lam mu i j

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_LatticePath_ext
  {N : ℕ}
  {a c : ℤ}
  {p q : LatticePath (N := N) a c}
-- given
  (h : p.eastStepHeights = q.eastStepHeights) :
-- imply
  p = q := by
-- proof
  apply SymmetricFunctions.LatticePath.ext h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_symToLatticePath_toSym
  {N : ℕ}
  {a c : ℤ}
-- given
  (p : LatticePath (N := N) a c) :
-- imply
  symToLatticePath p.toSym = p := by
-- proof
  apply SymmetricFunctions.symToLatticePath_toSym p

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_toSym_symToLatticePath
  {N : ℕ}
  {a c : ℤ}
-- given
  (s : Sym (Fin N) (c - a).toNat) :
-- imply
  (symToLatticePath s).toSym = s := by
-- proof
  apply SymmetricFunctions.toSym_symToLatticePath s

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_symToLatticePath_weight
  [CommRing R]
  {N : ℕ}
  {a c : ℤ}
-- given
  (s : Sym (Fin N) (c - a).toNat) :
-- imply
  (symToLatticePath s).weight (R := R) = (s.1.map (fun j => X j)).prod := by
-- proof
  apply SymmetricFunctions.symToLatticePath_weight s

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_pathWeightSum_eq_hsymm
  [CommRing R]
  {N : ℕ}
-- given
  (a c : ℤ) :
-- imply
  ∑ p ∈ latticePathFinset (N := N) a c, p.weight (R := R) = hsymmExt (N := N) (R := R) (c - a) := by
-- proof
  apply SymmetricFunctions.pathWeightSum_eq_hsymm a c

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_eq_of_paths_eq
  {N : ℕ}
  {lam mu : Fin N → ℕ}
  {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
  {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
  {hcontained : ∀ i, mu i ≤ lam i}
-- given
  (np1 np2 : Nipat lam mu hlam hmu hcontained)
  (h : np1.paths = np2.paths) :
-- imply
  np1 = np2 := by
-- proof
  apply SymmetricFunctions.Nipat.eq_of_paths_eq np1 np2 h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_ssytToNipat_nipatToSSYT
  {N : ℕ}
  {lam mu : Fin N → ℕ}
  {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
  {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
  {hcontained : ∀ i, mu i ≤ lam i}
-- given
  (np : Nipat lam mu hlam hmu hcontained) :
-- imply
  ssytToNipat (nipatToSSYT np) = np := by
-- proof
  apply SymmetricFunctions.ssytToNipat_nipatToSSYT np

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_nipat_path_length
  {N : ℕ}
  {lam mu : Fin N → ℕ}
  {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
  {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
  {hcontained : ∀ i, mu i ≤ lam i}
-- given
  (np : Nipat lam mu hlam hmu hcontained)
  (i : Fin N) :
-- imply
  (np.paths i).eastStepHeights.length = lam i - mu i := by
-- proof
  apply SymmetricFunctions.nipat_path_length np i

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_nipatToSSYT_entries
  {N : ℕ}
  {lam mu : Fin N → ℕ}
  {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
  {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
  {hcontained : ∀ i, mu i ≤ lam i}
-- given
  (np : Nipat lam mu hlam hmu hcontained)
  (i : Fin N)
  (k : Fin (lam i - mu i)) :
-- imply
  (nipatToSSYT np).entries i k = (np.paths i).eastStepHeights.get ⟨k.val, by simp [nipat_path_length]⟩ := by
-- proof
  apply SymmetricFunctions.nipatToSSYT_entries np i k

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_ssytToNipat_paths
  {N : ℕ}
  {lam mu : Fin N → ℕ}
  {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
  {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
  {hcontained : ∀ i, mu i ≤ lam i}
-- given
  (i : Fin N)
  (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩)
  (k : Fin (lam i - mu i)) :
-- imply
  ((ssytToNipat T).paths i).eastStepHeights.get ⟨k.val, by simp [nipat_path_length]⟩ = T.entries i k := by
-- proof
  apply SymmetricFunctions.ssytToNipat_paths T i k

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_nipatToSSYT_ssytToNipat
  {N : ℕ}
  {lam mu : Fin N → ℕ}
  {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
  {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
  {hcontained : ∀ i, mu i ≤ lam i}
-- given
  (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩) :
-- imply
  nipatToSSYT (ssytToNipat T) = T := by
-- proof
  apply SymmetricFunctions.nipatToSSYT_ssytToNipat T

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_nipatToSSYT_weight
  [CommRing R]
  {N : ℕ}
  {lam mu : Fin N → ℕ}
  {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
  {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
  {hcontained : ∀ i, mu i ≤ lam i}
-- given
  (np : Nipat lam mu hlam hmu hcontained) :
-- imply
  np.weight (R := R) = (nipatToSSYT np).toMonomial := by
-- proof
  apply SymmetricFunctions.nipatToSSYT_weight np

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_nipat_ssyt_bijection
  [CommRing R]
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
  (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
  (hcontained : ∀ i, mu i ≤ lam i) :
-- imply
  ∃ f : Nipat lam mu hlam hmu hcontained → SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩, Function.Bijective f ∧ ∀ np, np.weight (R := R) = (f np).toMonomial := by
-- proof
  apply SymmetricFunctions.nipat_ssyt_bijection lam mu hlam hmu hcontained

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_nipatWeightSum_eq_ssytSum
  [CommRing R]
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
  (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
  (hcontained : ∀ i, mu i ≤ lam i) :
-- imply
  ∑ np : Nipat lam mu hlam hmu hcontained, np.weight (R := R) = ∑ T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩, T.toMonomial := by
-- proof
  apply SymmetricFunctions.nipatWeightSum_eq_ssytSum lam mu hlam hmu hcontained

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_nipatWeightSum_eq_skewSchur
  [CommRing R]
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
  (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
  (hcontained : ∀ i, mu i ≤ lam i) :
-- imply
  ∑ np : Nipat lam mu hlam hmu hcontained, np.weight (R := R) = skewSchur (R := R) ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ := by
-- proof
  apply SymmetricFunctions.nipatWeightSum_eq_skewSchur lam mu hlam hmu hcontained

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_jacobiTrudiSourceVertex_xDecreasing
  {N : ℕ}
-- given
  (mu : Fin N → ℕ)
  (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i) :
-- imply
  LGV.xDecreasing (jacobiTrudiSourceVertex mu) := by
-- proof
  apply SymmetricFunctions.jacobiTrudiSourceVertex_xDecreasing mu hmu

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_jacobiTrudiSourceVertex_yIncreasing
  {N : ℕ}
-- given
  (mu : Fin N → ℕ) :
-- imply
  LGV.yIncreasing (jacobiTrudiSourceVertex mu) := by
-- proof
  apply SymmetricFunctions.jacobiTrudiSourceVertex_yIncreasing mu

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_jacobiTrudiTargetVertex_xDecreasing
  {N : ℕ}
-- given
  (lam : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
-- imply
  LGV.xDecreasing (jacobiTrudiTargetVertex lam) := by
-- proof
  apply SymmetricFunctions.jacobiTrudiTargetVertex_xDecreasing lam hlam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_jacobiTrudiTargetVertex_yIncreasing
  {N : ℕ}
-- given
  (lam : Fin N → ℕ) :
-- imply
  LGV.yIncreasing (jacobiTrudiTargetVertex lam) := by
-- proof
  apply SymmetricFunctions.jacobiTrudiTargetVertex_yIncreasing lam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgvPathEastStepYCoords_length_eq_xDisplacement
-- given
  (vertices : List (ℤ × ℤ))
  (h_ne : vertices ≠ [])
  (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)) :
-- imply
  (lgvPathEastStepYCoords vertices).length = ((vertices.getLast h_ne).1 - (vertices.head h_ne).1).toNat := by
-- proof
  apply SymmetricFunctions.lgvPathEastStepYCoords_length_eq_xDisplacement vertices h_ne h_arcs

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgvPathEastStepYCoords_weaklyIncreasing
-- given
  (vertices : List (ℤ × ℤ))
  (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)) :
-- imply
  (lgvPathEastStepYCoords vertices).IsChain (· ≤ ·) := by
-- proof
  apply SymmetricFunctions.lgvPathEastStepYCoords_weaklyIncreasing vertices h_arcs

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgvPathEastStepYCoords_bounded
-- given
  (vertices : List (ℤ × ℤ))
  (y : ℤ)
  (h_ne : vertices ≠ [])
  (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩))
  (hy : y ∈ lgvPathEastStepYCoords vertices) :
-- imply
  (vertices.head h_ne).2 ≤ y ∧ y ≤ (vertices.getLast h_ne).2 := by
-- proof
  apply SymmetricFunctions.lgvPathEastStepYCoords_bounded vertices h_ne h_arcs y hy

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgvPathEastStepYCoords_at_x
-- given
  (p : LGV.SimpleDigraph.Path LGV.integerLattice)
  (k : ℕ)
  (hk : k < (lgvPathEastStepYCoords p.vertices).length) :
-- imply
  ∃ (idx : ℕ) (hidx : idx < p.vertices.length), (p.vertices.get ⟨idx, hidx⟩).1 = p.start.1 + k ∧ (p.vertices.get ⟨idx, hidx⟩).2 = (lgvPathEastStepYCoords p.vertices)[k] := by
-- proof
  apply SymmetricFunctions.lgvPathEastStepYCoords_at_x p k hk

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgvPathEastStepYCoords_at_x_is_east_step
-- given
  (p : LGV.SimpleDigraph.Path LGV.integerLattice)
  (k idx : ℕ)
  (hk : k < (lgvPathEastStepYCoords p.vertices).length)
  (hidx : idx < p.vertices.length)
  (hx : (p.vertices.get ⟨idx, hidx⟩).1 = p.start.1 + k)
  (hy : (p.vertices.get ⟨idx, hidx⟩).2 = (lgvPathEastStepYCoords p.vertices)[k])
  (hidx_next : idx + 1 < p.vertices.length) :
-- imply
  (p.vertices.get ⟨idx + 1, hidx_next⟩).1 = (p.vertices.get ⟨idx, hidx⟩).1 + 1 ∧ (p.vertices.get ⟨idx + 1, hidx_next⟩).2 = (p.vertices.get ⟨idx, hidx⟩).2 := by
-- proof
  apply SymmetricFunctions.lgvPathEastStepYCoords_at_x_is_east_step p k hk idx hidx hx hy hidx_next

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_paths_above_at_x_stays_above
-- given
  (p p' : LGV.SimpleDigraph.Path LGV.integerLattice)
  (x₀ x₁ : ℤ)
  (hni : ∀ v, v ∈ p.vertices → v ∉ p'.vertices)
  (hx₀_p : ∃ (idx : ℕ) (hidx : idx < p.vertices.length), (p.vertices.get ⟨idx, hidx⟩).1 = x₀)
  (hx₀_p' : ∃ (idx : ℕ) (hidx : idx < p'.vertices.length), (p'.vertices.get ⟨idx, hidx⟩).1 = x₀)
  (h_above : ∀ (idx_p : ℕ) (hidx_p : idx_p < p.vertices.length) (idx_p' : ℕ) (hidx_p' : idx_p' < p'.vertices.length), (p.vertices.get ⟨idx_p, hidx_p⟩).1 = x₀ → (p'.vertices.get ⟨idx_p', hidx_p'⟩).1 = x₀ → (p'.vertices.get ⟨idx_p', hidx_p'⟩).2 > (p.vertices.get ⟨idx_p, hidx_p⟩).2)
  (hx₁ : x₁ ≥ x₀)
  (hx₁_p : ∃ (idx : ℕ) (hidx : idx < p.vertices.length), (p.vertices.get ⟨idx, hidx⟩).1 = x₁)
  (hx₁_p' : ∃ (idx : ℕ) (hidx : idx < p'.vertices.length), (p'.vertices.get ⟨idx, hidx⟩).1 = x₁) :
-- imply
  ∀ (idx_p : ℕ) (hidx_p : idx_p < p.vertices.length) (idx_p' : ℕ) (hidx_p' : idx_p' < p'.vertices.length), (p.vertices.get ⟨idx_p, hidx_p⟩).1 = x₁ → (p'.vertices.get ⟨idx_p', hidx_p'⟩).1 = x₁ → (p'.vertices.get ⟨idx_p', hidx_p'⟩).2 > (p.vertices.get ⟨idx_p, hidx_p⟩).2 := by
-- proof
  apply SymmetricFunctions.paths_above_at_x_stays_above p p' hni x₀ hx₀_p hx₀_p' h_above x₁ hx₁ hx₁_p hx₁_p'

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgvYCoordsToFinN_length
  {N : ℕ}
-- given
  (ycoords : List ℤ)
  (h : ∀ y ∈ ycoords, 1 ≤ y ∧ y ≤ N) :
-- imply
  (lgvYCoordsToFinN ycoords h).length = ycoords.length := by
-- proof
  apply SymmetricFunctions.lgvYCoordsToFinN_length ycoords h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgvYCoordsToFinN_getElem
  {N : ℕ}
-- given
  (ycoords : List ℤ)
  (k : ℕ)
  (h : ∀ y ∈ ycoords, 1 ≤ y ∧ y ≤ N)
  (hk : k < ycoords.length)
  (hk' : k < (lgvYCoordsToFinN ycoords h).length := by rwa [lgvYCoordsToFinN_length]) :
-- imply
  (lgvYCoordsToFinN ycoords h)[k].val + 1 = ycoords[k] := by
-- proof
  apply SymmetricFunctions.lgvYCoordsToFinN_getElem ycoords h k hk hk'

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgvYCoordsToFinN_isChain
  {N : ℕ}
-- given
  (ycoords : List ℤ)
  (h : ∀ y ∈ ycoords, 1 ≤ y ∧ y ≤ N)
  (hchain : ycoords.IsChain (· ≤ ·)) :
-- imply
  (lgvYCoordsToFinN ycoords h).IsChain (· ≤ ·) := by
-- proof
  apply SymmetricFunctions.lgvYCoordsToFinN_isChain ycoords h hchain

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgvYCoordsToFinN_injective
  {N : ℕ}
-- given
  (l₁ l₂ : List ℤ)
  (h₀ : ∀ y ∈ l₁, 1 ≤ y ∧ y ≤ N)
  (h₁ : ∀ y ∈ l₂, 1 ≤ y ∧ y ≤ N)
  (heq : lgvYCoordsToFinN l₁ h₀ = lgvYCoordsToFinN l₂ h₁) :
-- imply
  l₁ = l₂ := by
-- proof
  apply SymmetricFunctions.lgvYCoordsToFinN_injective l₁ l₂ h₀ h₁ heq

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgvYCoordsToFinN_map_val_add_one_eq
  {N : ℕ}
  {l : List ℤ}
-- given
  (heights : List (Fin N))
  (heq : l = heights.map (fun h => (h.val : ℤ) + 1))
  (h : ∀ y ∈ l, 1 ≤ y ∧ y ≤ N) :
-- imply
  lgvYCoordsToFinN l h = heights := by
-- proof
  apply SymmetricFunctions.lgvYCoordsToFinN_map_val_add_one_eq heights heq h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgvPath_vertices_eq_of_eastStepYCoords_eq
-- given
  (p₁ p₂ : LGV.SimpleDigraph.Path LGV.integerLattice)
  (hstart : p₁.start = p₂.start)
  (hfinish : p₁.finish = p₂.finish)
  (hcoords : lgvPathEastStepYCoords p₁.vertices = lgvPathEastStepYCoords p₂.vertices) :
-- imply
  p₁.vertices = p₂.vertices := by
-- proof
  apply SymmetricFunctions.lgvPath_vertices_eq_of_eastStepYCoords_eq p₁ p₂ hstart hfinish hcoords

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgvPathToLatticePath_injective
  {N : ℕ}
-- given
  (a c : ℤ)
  (p₁ p₂ : LGV.SimpleDigraph.Path LGV.integerLattice)
  (hstart₁ : p₁.start = (a, 1))
  (hfinish₁ : p₁.finish = (c, (N : ℤ)))
  (hstart₂ : p₂.start = (a, 1))
  (hfinish₂ : p₂.finish = (c, (N : ℤ)))
  (heq : lgvPathToLatticePath a c p₁ hstart₁ hfinish₁ = lgvPathToLatticePath a c p₂ hstart₂ hfinish₂) :
-- imply
  p₁ = p₂ := by
-- proof
  apply SymmetricFunctions.lgvPathToLatticePath_injective a c p₁ p₂ hstart₁ hfinish₁ hstart₂ hfinish₂ heq

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgvPathToLatticePath_weight_eq
  [CommRing R]
  {N : ℕ}
-- given
  (a c : ℤ)
  (p : LGV.SimpleDigraph.Path LGV.integerLattice)
  (hstart : p.start = (a, 1))
  (hfinish : p.finish = (c, (N : ℤ))) :
-- imply
  LGV.pathWeight (jacobiTrudiArcWeight (N := N) (R := R)) p = (lgvPathToLatticePath a c p hstart hfinish).weight (R := R) := by
-- proof
  apply SymmetricFunctions.lgvPathToLatticePath_weight_eq a c p hstart hfinish

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgv_pathWeightSum_eq_latticePathSum
  [CommRing R]
  {N : ℕ}
-- given
  (a c : ℤ)
  (h : 0 ≤ c - a)
  (hN : 0 < N) :
-- imply
  LGV.pathWeightSum LGV.integerLattice_pathFinite (jacobiTrudiArcWeight (N := N) (R := R)) (a, 1) (c, (N : ℤ)) = ∑ lp : LatticePath (N := N) a c, lp.weight (R := R) := by
-- proof
  apply SymmetricFunctions.lgv_pathWeightSum_eq_latticePathSum a c h hN

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgv_pathWeightSum_eq_hsymmExt
  [CommRing R]
  {N : ℕ}
-- given
  (hN : 0 < N)
  (a c : ℤ) :
-- imply
  LGV.pathWeightSum LGV.integerLattice_pathFinite (jacobiTrudiArcWeight (N := N) (R := R)) (a, 1) (c, (N : ℤ)) = hsymmExt (N := N) (R := R) (c - a) := by
-- proof
  apply SymmetricFunctions.lgv_pathWeightSum_eq_hsymmExt a c hN

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_jacobiTrudiMatrixH_eq_pathWeightMatrix_transpose
  [CommRing R]
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ) :
-- imply
  jacobiTrudiMatrixH (R := R) lam mu = (LGV.pathWeightMatrix LGV.integerLattice_pathFinite (jacobiTrudiArcWeight (N := N) (R := R)) (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam))ᵀ := by
-- proof
  apply SymmetricFunctions.jacobiTrudiMatrixH_eq_pathWeightMatrix_transpose lam mu

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_det_jacobiTrudiMatrixH_eq_det_pathWeightMatrix
  [CommRing R]
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ) :
-- imply
  (jacobiTrudiMatrixH (R := R) lam mu).det = (LGV.pathWeightMatrix LGV.integerLattice_pathFinite (jacobiTrudiArcWeight (N := N) (R := R)) (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam)).det := by
-- proof
  apply SymmetricFunctions.det_jacobiTrudiMatrixH_eq_det_pathWeightMatrix lam mu

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_lgv_nipatWeightSum_eq_nipatSum
  [CommRing R]
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
  (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
  (hcontained : ∀ i, mu i ≤ lam i) :
-- imply
  LGV.nipatWeightSum LGV.integerLattice_pathFinite (jacobiTrudiArcWeight (N := N) (R := R)) (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam) (Equiv.refl (Fin N)) = ∑ np : Nipat lam mu hlam hmu hcontained, np.weight (R := R) := by
-- proof
  apply SymmetricFunctions.lgv_nipatWeightSum_eq_nipatSum lam mu hlam hmu hcontained

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_det_jacobiTrudiMatrixH_eq_nipatSum
  [CommRing R]
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
  (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
  (hcontained : ∀ i, mu i ≤ lam i) :
-- imply
  (jacobiTrudiMatrixH (R := R) lam mu).det = ∑ np : Nipat lam mu hlam hmu hcontained, np.weight (R := R) := by
-- proof
  apply SymmetricFunctions.det_jacobiTrudiMatrixH_eq_nipatSum lam mu hlam hmu hcontained

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_jacobiTrudi_h
  [CommRing R]
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
  (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
  (hcontained : ∀ i, mu i ≤ lam i) :
-- imply
  skewSchur (R := R) ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ = (jacobiTrudiMatrixH (R := R) lam mu).det := by
-- proof
  apply SymmetricFunctions.jacobiTrudi_h lam mu hlam hmu hcontained

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_schur_eq_skewSchur_zero
  [CommRing R]
  {N : ℕ}
-- given
  (lam : SymmetricFunctions.NPartition N) :
-- imply
  schur (R := R) lam = skewSchur (R := R) ⟨lam, 0, fun _ => Nat.zero_le _⟩ := by
-- proof
  apply SymmetricFunctions.schur_eq_skewSchur_zero lam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_jacobiTrudi_h_nonSkew
  [CommRing R]
  {N : ℕ}
-- given
  (lam : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
-- imply
  schur (R := R) ⟨lam, hlam⟩ = (jacobiTrudiMatrixH (R := R) lam (fun _ => 0)).det := by
-- proof
  apply SymmetricFunctions.jacobiTrudi_h_nonSkew lam hlam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_det_isSymmetric_of_entries_symmetric
  [CommRing R]
  {N : ℕ}
-- given
  (M : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) R))
  (h : ∀ i j, (M i j).IsSymmetric) :
-- imply
  M.det.IsSymmetric := by
-- proof
  apply SymmetricFunctions.det_isSymmetric_of_entries_symmetric M h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_jacobiTrudiMatrixH_entries_isSymmetric
  [CommRing R]
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ)
  (i j : Fin N) :
-- imply
  (jacobiTrudiMatrixH (R := R) lam mu i j).IsSymmetric := by
-- proof
  apply SymmetricFunctions.jacobiTrudiMatrixH_entries_isSymmetric lam mu i j

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_jacobiTrudiMatrixH_det_isSymmetric
  [CommRing R]
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ) :
-- imply
  (jacobiTrudiMatrixH (R := R) lam mu).det.IsSymmetric := by
-- proof
  apply SymmetricFunctions.jacobiTrudiMatrixH_det_isSymmetric lam mu

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_skewSchur_isSymmetric_jacobiTrudi
  [CommRing R]
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
  (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
  (hcontained : ∀ i, mu i ≤ lam i) :
-- imply
  (skewSchur (R := R) ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩).IsSymmetric := by
-- proof
  apply SymmetricFunctions.skewSchur_isSymmetric_jacobiTrudi lam mu hlam hmu hcontained

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pjt_schur_isSymmetric_jacobiTrudi
  [CommRing R]
  {N : ℕ}
-- given
  (lam : Fin N → ℕ)
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
-- imply
  (schur (R := R) ⟨lam, hlam⟩).IsSymmetric := by
-- proof
  apply SymmetricFunctions.schur_isSymmetric_jacobiTrudi lam hlam

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_sum_card_filter_eq_sum_card_filter
  {N M : ℕ}
  (P : Fin N → Fin M → Prop)
  [∀ i j, Decidable (P i j)] :
-- imply
  ∑ i : Fin N, (Finset.univ.filter fun j : Fin M => P i j).card = ∑ j : Fin M, (Finset.univ.filter fun i : Fin N => P i j).card := by
-- proof
  apply SymmetricFunctions.NPartition.sum_card_filter_eq_sum_card_filter P

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_card_filter_le_fin
  {N : ℕ}
-- given
  (i : Fin N) :
-- imply
  (Finset.univ.filter fun r : Fin N => r ≤ i).card = i.val + 1 := by
-- proof
  apply SymmetricFunctions.NPartition.card_filter_le_fin i

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_multiset_prod_eq_sorted_prod
  [LinearOrder α]
  [CommMonoid β]
-- given
  (m : Multiset α)
  (f : α → β) :
-- imply
  (m.map f).prod = ((m.sort (· ≤ ·)).map f).prod := by
-- proof
  apply SymmetricFunctions.multiset_prod_eq_sorted_prod m f

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_list_prod_map_eq_fin_prod
  [CommMonoid β]
-- given
  (L : List α)
  (f : α → β) :
-- imply
  (L.map f).prod = ∏ j : Fin L.length, f (L.get j) := by
-- proof
  apply SymmetricFunctions.list_prod_map_eq_fin_prod L f

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_sorted_weakly_increasing
  [LinearOrder α]
-- given
  (m : Multiset α) :
-- imply
  ∀ i j : Fin (m.sort (· ≤ ·)).length, i ≤ j → (m.sort (· ≤ ·)).get i ≤ (m.sort (· ≤ ·)).get j := by
-- proof
  apply SymmetricFunctions.sorted_weakly_increasing m

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_sort_weaklyIncreasing_list_eq
  {N n : ℕ}
-- given
  (f : Fin n → Fin N)
  (hf : ∀ i j, i ≤ j → f i ≤ f j) :
-- imply
  ((Multiset.ofList ((List.finRange n).map f)).sort (· ≤ ·)) = (List.finRange n).map f := by
-- proof
  apply SymmetricFunctions.sort_weaklyIncreasing_list_eq f hf

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_prod_fin_ite
  [CommMonoid α]
  (P : Prop)
  [Decidable P]
  (f : Fin (if P then 1 else 0) → α) :
-- imply
  ∏ j : Fin (if P then 1 else 0), f j = if h : P then f ⟨0, by simp [h]⟩ else 1 := by
-- proof
  apply SymmetricFunctions.prod_fin_ite P f

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_list_map_prod_eq_finset_prod
  [DecidableEq α]
  [CommMonoid M]
-- given
  (l : List α)
  (hl : l.Nodup)
  (f : α → M) :
-- imply
  (l.map f).prod = ∏ x ∈ l.toFinset, f x := by
-- proof
  apply SymmetricFunctions.list_map_prod_eq_finset_prod l f hl

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_getElem_le_getElem_of_le
  [Preorder α]
  {l : List α}
  {i j : ℕ}
-- given
  (h : l.IsChain (· ≤ ·))
  (hi : i < l.length)
  (hj : j < l.length)
  (hij : i ≤ j) :
-- imply
  l[i] ≤ l[j] := by
-- proof
  apply SymmetricFunctions.List.IsChain.getElem_le_getElem_of_le h hi hj hij

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_list_prod_map_X_eq_finset_prod
  [CommRing R]
  {N : ℕ}
-- given
  (l : List (Fin N))
  (n : ℕ)
  (h : l.length = n) :
-- imply
  (l.map (fun j => MvPolynomial.X (R := R) j)).prod = ∏ k : Fin n, MvPolynomial.X (l.get ⟨k.val, h.symm ▸ k.isLt⟩) := by
-- proof
  apply SymmetricFunctions.list_prod_map_X_eq_finset_prod l n h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_x_coord_monotone_along_path
-- given
  (vertices : List (ℤ × ℤ))
  (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩))
  (h_ne : vertices ≠ []) :
-- imply
  (vertices.head h_ne).1 ≤ (vertices.getLast h_ne).1 := by
-- proof
  apply SymmetricFunctions.x_coord_monotone_along_path vertices h_arcs h_ne

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_lgvPath_y_nondecreasing
-- given
  (vertices : List (ℤ × ℤ))
  (i j : ℕ)
  (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩))
  (hi : i < vertices.length)
  (hj : j < vertices.length)
  (hij : i ≤ j) :
-- imply
  (vertices.get ⟨i, hi⟩).2 ≤ (vertices.get ⟨j, hj⟩).2 := by
-- proof
  apply SymmetricFunctions.lgvPath_y_nondecreasing vertices h_arcs i j hi hj hij

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_lgvPathEastStepYCoords_mem
-- given
  (vertices : List (ℤ × ℤ))
  (y : ℤ)
  (hy : y ∈ lgvPathEastStepYCoords vertices) :
-- imply
  ∃ i : ℕ, ∃ hi : i < vertices.length, (vertices.get ⟨i, hi⟩).2 = y := by
-- proof
  apply SymmetricFunctions.lgvPathEastStepYCoords_mem vertices y hy

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_lgvPathEastStepYCoords_head_mem
-- given
  (vertices : List (ℤ × ℤ))
  (y : ℤ)
  (hy : y ∈ (lgvPathEastStepYCoords vertices).head?) :
-- imply
  ∃ i : ℕ, ∃ hi : i < vertices.length, (vertices.get ⟨i, hi⟩).2 = y := by
-- proof
  apply SymmetricFunctions.lgvPathEastStepYCoords_head_mem vertices y hy

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_lgvPathEastStepYCoords_ge_start
-- given
  (vertices : List (ℤ × ℤ))
  (y : ℤ)
  (h_ne : vertices ≠ [])
  (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩))
  (hy : y ∈ lgvPathEastStepYCoords vertices) :
-- imply
  (vertices.head h_ne).2 ≤ y := by
-- proof
  apply SymmetricFunctions.lgvPathEastStepYCoords_ge_start vertices h_ne h_arcs y hy

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_lgvPathEastStepYCoords_head_ge_start
-- given
  (vertices : List (ℤ × ℤ))
  (y : ℤ)
  (h_ne : vertices ≠ [])
  (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩))
  (hy : y ∈ (lgvPathEastStepYCoords vertices).head?) :
-- imply
  (vertices.head h_ne).2 ≤ y := by
-- proof
  apply SymmetricFunctions.lgvPathEastStepYCoords_head_ge_start vertices h_ne h_arcs y hy

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_lgvPathEastStepYCoords_at_x_aux
-- given
  (vertices : List (ℤ × ℤ))
  (k : ℕ)
  (h_ne : vertices ≠ [])
  (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩))
  (hk : k < (lgvPathEastStepYCoords vertices).length) :
-- imply
  ∃ (idx : ℕ) (hidx : idx < vertices.length), (vertices.get ⟨idx, hidx⟩).1 = (vertices.head h_ne).1 + k ∧ (vertices.get ⟨idx, hidx⟩).2 = (lgvPathEastStepYCoords vertices)[k] ∧ (∀ hidx_next : idx + 1 < vertices.length, (vertices.get ⟨idx + 1, hidx_next⟩).1 = (vertices.get ⟨idx, hidx⟩).1 + 1 ∧ (vertices.get ⟨idx + 1, hidx_next⟩).2 = (vertices.get ⟨idx, hidx⟩).2) := by
-- proof
  apply SymmetricFunctions.lgvPathEastStepYCoords_at_x_aux vertices h_ne h_arcs k hk

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_integerLattice_path_x_monotone
-- given
  (p : LGV.SimpleDigraph.Path LGV.integerLattice)
  (i j : ℕ)
  (hi : i < p.vertices.length)
  (hj : j < p.vertices.length)
  (hij : i ≤ j) :
-- imply
  (p.vertices.get ⟨i, hi⟩).1 ≤ (p.vertices.get ⟨j, hj⟩).1 := by
-- proof
  apply SymmetricFunctions.integerLattice_path_x_monotone p i j hi hj hij

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_integerLattice_path_x_lt_implies_idx_lt
-- given
  (p : LGV.SimpleDigraph.Path LGV.integerLattice)
  (i j : ℕ)
  (hi : i < p.vertices.length)
  (hj : j < p.vertices.length)
  (hx : (p.vertices.get ⟨i, hi⟩).1 < (p.vertices.get ⟨j, hj⟩).1) :
-- imply
  i < j := by
-- proof
  apply SymmetricFunctions.integerLattice_path_x_lt_implies_idx_lt p i j hi hj hx

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_integerLattice_path_y_contiguous_at_x
-- given
  (p : LGV.SimpleDigraph.Path LGV.integerLattice)
  (x₀ : ℤ)
  (i j : ℕ)
  (y : ℤ)
  (hi : i < p.vertices.length)
  (hj : j < p.vertices.length)
  (hij : i ≤ j)
  (hx_i : (p.vertices.get ⟨i, hi⟩).1 = x₀)
  (hx_j : (p.vertices.get ⟨j, hj⟩).1 = x₀)
  (hy_lo : (p.vertices.get ⟨i, hi⟩).2 ≤ y)
  (hy_hi : y ≤ (p.vertices.get ⟨j, hj⟩).2) :
-- imply
  ∃ (k : ℕ) (hk : k < p.vertices.length), i ≤ k ∧ k ≤ j ∧ (p.vertices.get ⟨k, hk⟩).1 = x₀ ∧ (p.vertices.get ⟨k, hk⟩).2 = y := by
-- proof
  apply SymmetricFunctions.integerLattice_path_y_contiguous_at_x p x₀ i j hi hj hij hx_i hx_j y hy_lo hy_hi

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_coordSum_strict_inc
-- given
  (u v : ℤ × ℤ)
  (h : LGV.integerLattice.arc u v) :
-- imply
  u.1 + u.2 < v.1 + v.2 := by
-- proof
  apply SymmetricFunctions.coordSum_strict_inc u v h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_coordSum_head_le_last
-- given
  (vertices : List (ℤ × ℤ))
  (h_ne : vertices ≠ [])
  (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)) :
-- imply
  (vertices.head h_ne).1 + (vertices.head h_ne).2 ≤ (vertices.getLast h_ne).1 + (vertices.getLast h_ne).2 := by
-- proof
  apply SymmetricFunctions.coordSum_head_le_last vertices h_ne h_arcs

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_coordSum_head_lt_last_of_length_ge_two
-- given
  (vertices : List (ℤ × ℤ))
  (h_ne : vertices ≠ [])
  (h_len : vertices.length ≥ 2)
  (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)) :
-- imply
  (vertices.head h_ne).1 + (vertices.head h_ne).2 < (vertices.getLast h_ne).1 + (vertices.getLast h_ne).2 := by
-- proof
  apply SymmetricFunctions.coordSum_head_lt_last_of_length_ge_two vertices h_ne h_len h_arcs

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_lgvPath_vertices_eq_aux
-- given
  (vs₁ vs₂ : List (ℤ × ℤ))
  (h_ne₁ : vs₁ ≠ [])
  (h_ne₂ : vs₂ ≠ [])
  (h_arcs₁ : ∀ i : ℕ, ∀ hi : i + 1 < vs₁.length, LGV.integerLattice.arc (vs₁.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vs₁.get ⟨i + 1, hi⟩))
  (h_arcs₂ : ∀ i : ℕ, ∀ hi : i + 1 < vs₂.length, LGV.integerLattice.arc (vs₂.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vs₂.get ⟨i + 1, hi⟩))
  (hstart : vs₁.head h_ne₁ = vs₂.head h_ne₂)
  (hfinish : vs₁.getLast h_ne₁ = vs₂.getLast h_ne₂)
  (hcoords : lgvPathEastStepYCoords vs₁ = lgvPathEastStepYCoords vs₂) :
-- imply
  vs₁ = vs₂ := by
-- proof
  apply SymmetricFunctions.lgvPath_vertices_eq_aux vs₁ vs₂ h_ne₁ h_ne₂ h_arcs₁ h_arcs₂ hstart hfinish hcoords

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVerticesAux_nonempty
-- given
  (N : ℕ)
  (heights : List (Fin N))
  (x y : ℤ)
  (fuel : ℕ) :
-- imply
  buildVerticesAux N x y heights fuel ≠ [] := by
-- proof
  apply SymmetricFunctions.buildVerticesAux_nonempty N x y heights fuel

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVertices_nonempty
-- given
  (a c : ℤ)
  (N : ℕ)
  (eastStepHeights : List (Fin N)) :
-- imply
  buildVertices a c N eastStepHeights ≠ [] := by
-- proof
  apply SymmetricFunctions.buildVertices_nonempty a c N eastStepHeights

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVerticesAux_head
-- given
  (N fuel : ℕ)
  (heights : List (Fin N))
  (hfuel : fuel ≥ 1 ∨ heights = [])
  (x y : ℤ) :
-- imply
  (buildVerticesAux N x y heights fuel).head (buildVerticesAux_nonempty N x y heights fuel) = (x, y) := by
-- proof
  apply SymmetricFunctions.buildVerticesAux_head N x y heights fuel hfuel

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVertices_head
-- given
  (N : ℕ)
  (hN : N ≥ 1)
  (a c : ℤ)
  (eastStepHeights : List (Fin N)) :
-- imply
  (buildVertices a c N eastStepHeights).head (buildVertices_nonempty a c N eastStepHeights) = (a, 1) := by
-- proof
  apply SymmetricFunctions.buildVertices_head a c N eastStepHeights hN

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVerticesAux_head_getElem
-- given
  (N : ℕ)
  (x y : ℤ)
  (fuel : ℕ)
  (heights : List (Fin N))
  (h : 0 < (buildVerticesAux N x y heights fuel).length) :
-- imply
  (buildVerticesAux N x y heights fuel)[0] = (x, y) := by
-- proof
  apply SymmetricFunctions.buildVerticesAux_head_getElem N x y heights fuel h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVerticesAux_length_pos
-- given
  (N : ℕ)
  (heights : List (Fin N))
  (x y : ℤ)
  (fuel : ℕ) :
-- imply
  0 < (buildVerticesAux N x y heights fuel).length := by
-- proof
  apply SymmetricFunctions.buildVerticesAux_length_pos N x y heights fuel

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVerticesAux_x_ge
-- given
  (N : ℕ)
  (x y : ℤ)
  (fuel idx : ℕ)
  (heights : List (Fin N))
  (hidx : idx < (buildVerticesAux N x y heights fuel).length) :
-- imply
  (buildVerticesAux N x y heights fuel)[idx].1 ≥ x := by
-- proof
  apply SymmetricFunctions.buildVerticesAux_x_ge N x y heights fuel idx hidx

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVerticesAux_y_upper_bound
-- given
  (N : ℕ)
  (x y : ℤ)
  (fuel idx j : ℕ)
  (heights : List (Fin N))
  (hfuel : fuel ≥ heights.length + (N - y.toNat))
  (hy : 1 ≤ y)
  (hyN : y ≤ N)
  (hchain : heights.IsChain (· ≤ ·))
  (hbounds : ∀ h ∈ heights, y ≤ (h.val : ℤ) + 1)
  (hidx : idx < (buildVerticesAux N x y heights fuel).length)
  (hj : j < heights.length)
  (hx_eq : (buildVerticesAux N x y heights fuel)[idx].1 = x + j) :
-- imply
  (buildVerticesAux N x y heights fuel)[idx].2 ≤ heights[j].val + 1 := by
-- proof
  apply SymmetricFunctions.buildVerticesAux_y_upper_bound N x y heights fuel hfuel hy hyN hchain hbounds idx hidx j hj hx_eq

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVerticesAux_y_ge
-- given
  (N : ℕ)
  (x y : ℤ)
  (fuel idx : ℕ)
  (heights : List (Fin N))
  (hidx : idx < (buildVerticesAux N x y heights fuel).length) :
-- imply
  (buildVerticesAux N x y heights fuel)[idx].2 ≥ y := by
-- proof
  apply SymmetricFunctions.buildVerticesAux_y_ge N x y heights fuel idx hidx

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVerticesAux_y_lower_bound
-- given
  (N : ℕ)
  (x y : ℤ)
  (fuel idx j : ℕ)
  (heights : List (Fin N))
  (hfuel : fuel ≥ heights.length + (N - y.toNat))
  (hy : 1 ≤ y)
  (hyN : y ≤ N)
  (hchain : heights.IsChain (· ≤ ·))
  (hbounds : ∀ h ∈ heights, y ≤ (h.val : ℤ) + 1)
  (hidx : idx < (buildVerticesAux N x y heights fuel).length)
  (hj : j < heights.length)
  (hj_pos : 0 < j)
  (hx_eq : (buildVerticesAux N x y heights fuel)[idx].1 = x + j) :
-- imply
  (buildVerticesAux N x y heights fuel)[idx].2 ≥ heights[j - 1].val + 1 := by
-- proof
  apply SymmetricFunctions.buildVerticesAux_y_lower_bound N x y heights fuel hfuel hy hyN hchain hbounds idx hidx j hj hj_pos hx_eq

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVerticesAux_arcs_valid
-- given
  (N : ℕ)
  (x y : ℤ)
  (fuel : ℕ)
  (heights : List (Fin N))
  (hfuel : fuel ≥ heights.length + (N - y.toNat))
  (hy : 1 ≤ y)
  (hyN : y ≤ N) :
-- imply
  ∀ i : ℕ, ∀ hi : i + 1 < (buildVerticesAux N x y heights fuel).length, LGV.integerLattice.arc ((buildVerticesAux N x y heights fuel).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((buildVerticesAux N x y heights fuel).get ⟨i + 1, hi⟩) := by
-- proof
  apply SymmetricFunctions.buildVerticesAux_arcs_valid N x y heights fuel hfuel hy hyN

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_toNat_add_one_of_nonneg
-- given
  (y : ℤ)
  (hy_pos : 0 ≤ y) :
-- imply
  (y + 1).toNat = y.toNat + 1 := by
-- proof
  apply SymmetricFunctions.toNat_add_one_of_nonneg y hy_pos

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVerticesAux_getLast
-- given
  (N : ℕ)
  (x y : ℤ)
  (fuel : ℕ)
  (heights : List (Fin N))
  (hfuel : fuel ≥ heights.length + (N - y.toNat))
  (hy : 1 ≤ y)
  (hyN : y ≤ N)
  (hN : 0 < N)
  (hchain : heights.IsChain (· ≤ ·))
  (hbounds : ∀ h ∈ heights, y ≤ (h.val : ℤ) + 1) :
-- imply
  (buildVerticesAux N x y heights fuel).getLast (buildVerticesAux_nonempty N x y heights fuel) = (x + heights.length, (N : ℤ)) := by
-- proof
  apply SymmetricFunctions.buildVerticesAux_getLast N x y heights fuel hfuel hy hyN hN hchain hbounds

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVertices_arcs_valid
-- given
  (a c : ℤ)
  (N : ℕ)
  (eastStepHeights : List (Fin N))
  (hN : 0 < N)
  (hlen : eastStepHeights.length = (c - a).toNat)
  (h : 0 ≤ c - a) :
-- imply
  ∀ i : ℕ, ∀ hi : i + 1 < (buildVertices a c N eastStepHeights).length, LGV.integerLattice.arc ((buildVertices a c N eastStepHeights).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((buildVertices a c N eastStepHeights).get ⟨i + 1, hi⟩) := by
-- proof
  apply SymmetricFunctions.buildVertices_arcs_valid a c N eastStepHeights hN hlen h

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVertices_getLast
-- given
  (a c : ℤ)
  (N : ℕ)
  (eastStepHeights : List (Fin N))
  (hN : 0 < N)
  (hlen : eastStepHeights.length = (c - a).toNat)
  (h : 0 ≤ c - a)
  (hchain : eastStepHeights.IsChain (· ≤ ·)) :
-- imply
  (buildVertices a c N eastStepHeights).getLast (buildVertices_nonempty a c N eastStepHeights) = (c, (N : ℤ)) := by
-- proof
  apply SymmetricFunctions.buildVertices_getLast a c N eastStepHeights hN hlen h hchain

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVertices_y_upper_bound_at_x
-- given
  (a c : ℤ)
  (N idx k : ℕ)
  (heights : List (Fin N))
  (hN : 0 < N)
  (hlen : heights.length = (c - a).toNat)
  (h : 0 ≤ c - a)
  (hchain : heights.IsChain (· ≤ ·))
  (hidx : idx < (buildVertices a c N heights).length)
  (hk : k < heights.length)
  (hx_eq : (buildVertices a c N heights)[idx].1 = a + k) :
-- imply
  (buildVertices a c N heights)[idx].2 ≤ heights[k].val + 1 := by
-- proof
  apply SymmetricFunctions.buildVertices_y_upper_bound_at_x a c N heights hN hlen h hchain idx hidx k hk hx_eq

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVertices_y_lower_bound_at_x
-- given
  (a c : ℤ)
  (N idx k : ℕ)
  (heights : List (Fin N))
  (hN : 0 < N)
  (hlen : heights.length = (c - a).toNat)
  (h : 0 ≤ c - a)
  (hchain : heights.IsChain (· ≤ ·))
  (hidx : idx < (buildVertices a c N heights).length)
  (hk : k < heights.length)
  (hk_pos : 0 < k)
  (hx_eq : (buildVertices a c N heights)[idx].1 = a + k) :
-- imply
  (buildVertices a c N heights)[idx].2 ≥ heights[k - 1].val + 1 := by
-- proof
  apply SymmetricFunctions.buildVertices_y_lower_bound_at_x a c N heights hN hlen h hchain idx hidx k hk hk_pos hx_eq

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVertices_y_lower_bound_at_last_column
-- given
  (a c : ℤ)
  (N idx : ℕ)
  (heights : List (Fin N))
  (hN : 0 < N)
  (hlen : heights.length = (c - a).toNat)
  (h : 0 ≤ c - a)
  (hchain : heights.IsChain (· ≤ ·))
  (hlen_pos : 0 < heights.length)
  (hidx : idx < (buildVertices a c N heights).length)
  (hx_eq : (buildVertices a c N heights)[idx].1 = a + heights.length) :
-- imply
  (buildVertices a c N heights)[idx].2 ≥ heights[heights.length - 1].val + 1 := by
-- proof
  apply SymmetricFunctions.buildVertices_y_lower_bound_at_last_column a c N heights hN hlen h hchain hlen_pos idx hidx hx_eq

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_pathWeightAux_eq_prod_eastStepYCoords
  [CommRing R]
  {N : ℕ}
-- given
  (vertices : List (ℤ × ℤ))
  (h_ne : vertices ≠ [])
  (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩))
  (h_bounded : ∀ y ∈ lgvPathEastStepYCoords vertices, 1 ≤ y ∧ y ≤ N) :
-- imply
  LGV.pathWeightAux (jacobiTrudiArcWeight (N := N) (R := R)) vertices h_arcs = ((lgvPathEastStepYCoords vertices).pmap (fun y hy => MvPolynomial.X (R := R) (⟨(y - 1).toNat, by have := h_bounded y hy; omega⟩ : Fin N)) (fun _ hy => hy)).prod := by
-- proof
  apply SymmetricFunctions.pathWeightAux_eq_prod_eastStepYCoords vertices h_ne h_arcs h_bounded

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_pathWeightAux_eq_map_prod_lgvYCoords
  [CommRing R]
  {N : ℕ}
-- given
  (vertices : List (ℤ × ℤ))
  (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩))
  (h_bounded : ∀ y ∈ lgvPathEastStepYCoords vertices, 1 ≤ y ∧ y ≤ N) :
-- imply
  LGV.pathWeightAux (jacobiTrudiArcWeight (N := N) (R := R)) vertices h_arcs = (List.map (fun j => X j) (lgvYCoordsToFinN (lgvPathEastStepYCoords vertices) h_bounded)).prod := by
-- proof
  apply SymmetricFunctions.pathWeightAux_eq_map_prod_lgvYCoords vertices h_arcs h_bounded

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_buildVerticesAux_head'
-- given
  (N : ℕ)
  (heights : List (Fin N))
  (x y : ℤ)
  (fuel : ℕ) :
-- imply
  ∃ tail, buildVerticesAux N x y heights fuel = (x, y) :: tail := by
-- proof
  apply SymmetricFunctions.buildVerticesAux_head' N x y heights fuel

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_lgvPathEastStepYCoords_cons_north_gen
-- given
  (x y : ℤ)
  (tail : List (ℤ × ℤ))
  (hhead : ∃ tail', tail = (x, y + 1) :: tail') :
-- imply
  lgvPathEastStepYCoords ((x, y) :: tail) = lgvPathEastStepYCoords tail := by
-- proof
  apply SymmetricFunctions.lgvPathEastStepYCoords_cons_north_gen x y tail hhead

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_lgvPathEastStepYCoords_cons_east_gen
-- given
  (x y : ℤ)
  (tail : List (ℤ × ℤ))
  (hhead : ∃ tail', tail = (x + 1, y) :: tail') :
-- imply
  lgvPathEastStepYCoords ((x, y) :: tail) = y :: lgvPathEastStepYCoords tail := by
-- proof
  apply SymmetricFunctions.lgvPathEastStepYCoords_cons_east_gen x y tail hhead

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_lgvPathEastStepYCoords_buildVerticesAux
-- given
  (N : ℕ)
  (x y : ℤ)
  (fuel : ℕ)
  (heights : List (Fin N))
  (hfuel : fuel ≥ heights.length + (N - y.toNat))
  (hy : 1 ≤ y)
  (hyN : y ≤ N)
  (hchain : heights.IsChain (· ≤ ·))
  (hbounds : ∀ h ∈ heights, y ≤ (h.val : ℤ) + 1) :
-- imply
  lgvPathEastStepYCoords (buildVerticesAux N x y heights fuel) = heights.map (fun h => (h.val : ℤ) + 1) := by
-- proof
  apply SymmetricFunctions.lgvPathEastStepYCoords_buildVerticesAux N x y heights fuel hfuel hy hyN hchain hbounds

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_lgvPathEastStepYCoords_buildVertices
  {N : ℕ}
-- given
  (a c : ℤ)
  (heights : List (Fin N))
  (hN : 0 < N)
  (hlen : heights.length = (c - a).toNat)
  (h : 0 ≤ c - a)
  (hchain : heights.IsChain (· ≤ ·)) :
-- imply
  lgvPathEastStepYCoords (buildVertices a c N heights) = heights.map (fun h => (h.val : ℤ) + 1) := by
-- proof
  apply SymmetricFunctions.lgvPathEastStepYCoords_buildVertices a c heights hN hlen h hchain

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_path_above_stays_above
-- given
  (p p' : LGV.SimpleDigraph.Path LGV.integerLattice)
  (s₀ s₁ : ℤ)
  (hni : ∀ v, v ∈ p.vertices → v ∉ p'.vertices)
  (hs₀_p : s₀ ≥ p.start.1 + p.start.2)
  (hs₀_p' : s₀ ≥ p'.start.1 + p'.start.2)
  (hs₀_p_end : s₀ ≤ p.finish.1 + p.finish.2)
  (hs₀_p'_end : s₀ ≤ p'.finish.1 + p'.finish.2)
  (h_above : ∀ (hidx_p : (s₀ - p.start.1 - p.start.2).toNat < p.vertices.length) (hidx_p' : (s₀ - p'.start.1 - p'.start.2).toNat < p'.vertices.length), (p'.vertices.get ⟨(s₀ - p'.start.1 - p'.start.2).toNat, hidx_p'⟩).2 > (p.vertices.get ⟨(s₀ - p.start.1 - p.start.2).toNat, hidx_p⟩).2)
  (hs₁ : s₁ ≥ s₀)
  (hs₁_p_end : s₁ ≤ p.finish.1 + p.finish.2)
  (hs₁_p'_end : s₁ ≤ p'.finish.1 + p'.finish.2) :
-- imply
  ∀ (hidx_p : (s₁ - p.start.1 - p.start.2).toNat < p.vertices.length) (hidx_p' : (s₁ - p'.start.1 - p'.start.2).toNat < p'.vertices.length), (p'.vertices.get ⟨(s₁ - p'.start.1 - p'.start.2).toNat, hidx_p'⟩).2 > (p.vertices.get ⟨(s₁ - p.start.1 - p.start.2).toNat, hidx_p⟩).2 := by
-- proof
  apply SymmetricFunctions.path_above_stays_above p p' hni s₀ hs₀_p hs₀_p' hs₀_p_end hs₀_p'_end h_above s₁ hs₁ hs₁_p_end hs₁_p'_end

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_isNonIntersecting_implies_colStrictPaths
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ)
  (pt : LGV.PathTuple LGV.integerLattice N (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam))
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
  (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
  (hcontained : ∀ i, mu i ≤ lam i)
  (hni : pt.isNonIntersecting) :
-- imply
  ∀ i j : Fin N, i < j → ∀ k : ℕ, ∀ hk : k < ((pathTupleToLatticePaths lam mu pt) i).eastStepHeights.length, ∀ k' : ℕ, ∀ hk' : k' < ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights.length, mu i + k = mu j + k' → ((pathTupleToLatticePaths lam mu pt) i).eastStepHeights[k] < ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights[k'] := by
-- proof
  apply SymmetricFunctions.isNonIntersecting_implies_colStrictPaths lam mu hlam hmu hcontained pt hni

/--
[PieriJacobiTrudi](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/PieriJacobiTrudi.lean)
-/
@[path]
private lemma pv_pathTupleToNipat_weight
  [CommRing R]
  {N : ℕ}
-- given
  (lam mu : Fin N → ℕ)
  (pt : LGV.PathTuple LGV.integerLattice N (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam))
  (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
  (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
  (hcontained : ∀ i, mu i ≤ lam i)
  (hni : pt.isNonIntersecting) :
-- imply
  LGV.pathTupleWeight (jacobiTrudiArcWeight (N := N) (R := R)) pt.paths = (pathTupleToNipat lam mu hlam hmu hcontained pt hni).weight (R := R) := by
-- proof
  apply SymmetricFunctions.pathTupleToNipat_weight lam mu hlam hmu hcontained pt hni


-- created on 2026-10-23
