import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.IntegerCompositions.Part17
open AlgebraicCombinatorics
open AlgebraicCombinatorics.BoundedWeakComposition
open Finset
open scoped BigOperators


section
-- ac-theorems


open Finset Nat BigOperators
set_option allowUnsafeReducibility true
attribute [local reducible] PNat

namespace AlgebraicCombinatorics

namespace Composition


/-- The size of the empty composition is 0. -/
@[simp]
lemma size_nil : size ([] : Composition) = 0 := rfl

/-- The length of the empty composition is 0. -/
@[simp]
lemma len_nil : len ([] : Composition) = 0 := rfl

/-- The size of a cons composition is the head value plus the tail size. -/
@[simp]
lemma size_cons (a : ℕ+) (α : Composition) : size (a :: α) = a.val + size α := rfl

/-- The length of a cons composition is the tail length plus 1. -/
@[simp]
lemma len_cons (a : ℕ+) (α : Composition) : len (a :: α) = len α + 1 := by
  simp only [len, List.length_cons]

/-- The size of a composition is at least its length, since each part is positive. -/
lemma size_ge_len (α : Composition) : α.len ≤ α.size := by
  induction α with
  | nil => simp
  | cons a as ih =>
    simp only [size_cons, len_cons]
    have ha : 1 ≤ a.val := a.pos
    omega

/-- The size of a singleton composition is the value of its single part. -/
@[simp]
lemma size_singleton (n : ℕ+) : (singleton n).size = n.val := by
  simp [singleton, size]

/-- The length of a singleton composition is 1. -/
@[simp]
lemma len_singleton (n : ℕ+) : (singleton n).len = 1 := rfl

/-- The size of the concatenation of two compositions equals the sum of their sizes. -/
@[simp]
lemma size_append (α β : Composition) : (α ++ β).size = α.size + β.size :=
  (congrArg List.sum (List.map_append (f := fun x : ℕ+ => x.val) (l₁ := α) (l₂ := β))).trans
    (List.sum_append (l₁ := List.map (fun x : ℕ+ => x.val) α)
      (l₂ := List.map (fun x : ℕ+ => x.val) β))

/-- The length of the concatenation of two compositions equals the sum of their lengths. -/
@[simp]
lemma len_append (α β : Composition) : (α ++ β).len = α.len + β.len :=
  List.length_append (as := α) (bs := β)

/--
The empty list is the only composition of size 0.
-/
lemma empty_of_size_zero (α : Composition) (h : α.size = 0) : α = [] := by
  cases α with
  | nil => rfl
  | cons x xs =>
    simp only [size, List.map_cons, List.sum_cons] at h
    have : 0 < x.val := x.pos
    omega

end Composition


namespace MathlibComposition

/--
Key lemma: for `n > 0`, the cardinality of the finset associated to a composition
equals the length minus 1.

This follows from the structure of the `compositionAsSetEquiv`: it extracts the
"interior" boundary points of a composition (those between 0 and n), and a
composition of length k has exactly k-1 such interior points.
-/
lemma compositionAsSetEquiv_card_eq_length_sub_one (n : ℕ) (hn : 0 < n)
    (c : CompositionAsSet n) : (compositionAsSetEquiv n c).card + 1 = c.length := by
  -- The equiv extracts interior boundary points (not 0 or Fin.last n)
  -- c.length = c.boundaries.card - 1
  -- Interior points = c.boundaries.card - 2 (removing 0 and Fin.last n)
  -- So equiv.card = c.length - 1, hence equiv.card + 1 = c.length
  unfold compositionAsSetEquiv
  simp only [Equiv.coe_fn_mk]
  have h1 : c.boundaries.card = c.length + 1 := c.card_boundaries_eq_succ_length
  -- Define the interior of the boundaries
  let interior := c.boundaries.filter (fun x => x ≠ 0 ∧ x ≠ Fin.last n)
  have h_interior_card : interior.card = c.boundaries.card - 2 := by
    have h0 : (0 : Fin n.succ) ∈ c.boundaries := c.zero_mem
    have hn_mem : Fin.last n ∈ c.boundaries := c.getLast_mem
    have h_ne : (0 : Fin n.succ) ≠ Fin.last n := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last]
      omega
    -- interior = c.boundaries \ {0, Fin.last n}
    have heq : interior = c.boundaries \ {0, Fin.last n} := by
      ext x
      simp only [interior, mem_filter, mem_sdiff, mem_insert, mem_singleton]
      tauto
    rw [heq]
    have hpair : {0, Fin.last n} ⊆ c.boundaries := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h0
      · exact hn_mem
    rw [Finset.card_sdiff_of_subset hpair, Finset.card_pair h_ne]
  -- The set {i : Fin (n-1) | ⟨1 + i, _⟩ ∈ c.boundaries} is in bijection with interior
  have h_card_eq : {i : Fin (n - 1) | (⟨1 + (i : ℕ), by omega⟩ : Fin n.succ) ∈ c.boundaries}.toFinset.card = interior.card := by
    apply Finset.card_bij (fun (i : Fin (n - 1)) _ => (⟨1 + (i : ℕ), by have := i.isLt; omega⟩ : Fin n.succ))
    · -- i_mem: the image is in interior
      intro i hi
      simp at hi
      simp only [interior, mem_filter]
      refine ⟨hi, ?_, ?_⟩
      · simp only [ne_eq, Fin.ext_iff, Fin.val_zero]
        omega
      · simp only [ne_eq, Fin.ext_iff, Fin.val_last]
        have : (i : ℕ) < n - 1 := i.isLt
        omega
    · -- i_inj: the map is injective
      intro i₁ _ i₂ _ heq
      simp only [Fin.ext_iff] at heq ⊢
      omega
    · -- i_surj: the map is surjective
      intro x hx
      simp only [interior, mem_filter] at hx
      obtain ⟨hx_mem, hx_ne0, hx_neL⟩ := hx
      have hx_pos : 0 < x.val := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_zero] at hx_ne0
        omega
      have hx_lt : x.val < n := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_last] at hx_neL
        have : x.val ≤ n := Nat.lt_succ_iff.mp x.isLt
        omega
      have hval : x.val - 1 < n - 1 := by omega
      refine ⟨⟨x.val - 1, hval⟩, ?_, ?_⟩
      · simp only [Set.mem_toFinset, Set.mem_ofPred_eq]
        convert hx_mem using 2
        omega
      · simp only [Fin.ext_iff]
        omega
  rw [h_card_eq, h_interior_card, h1]
  -- Now we have: (c.length + 1 - 2) + 1 = c.length when c.length ≥ 1
  have hlen_pos : 1 ≤ c.length := by
    have h2 : 2 ≤ c.boundaries.card := by
      have h0 : (0 : Fin n.succ) ∈ c.boundaries := c.zero_mem
      have hn_mem : Fin.last n ∈ c.boundaries := c.getLast_mem
      have h_ne : (0 : Fin n.succ) ≠ Fin.last n := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last]
        omega
      have : {0, Fin.last n} ⊆ c.boundaries := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      calc c.boundaries.card ≥ ({0, Fin.last n} : Finset (Fin n.succ)).card := Finset.card_le_card this
        _ = 2 := Finset.card_pair h_ne
    omega
  omega

/-- The cardinality of the associated finset plus 1 equals the composition length. -/
lemma compositionToFinset_card_add_one (n : ℕ) (hn : 0 < n) (c : _root_.Composition n) :
    (compositionToFinset n c).card + 1 = c.length := by
  simp only [compositionToFinset, Equiv.trans_apply, compositionEquiv]
  have h := compositionAsSetEquiv_card_eq_length_sub_one n hn c.toCompositionAsSet
  convert h using 1
  exact c.toCompositionAsSet_length.symm

/--
**Theorem thm.fps.comps.num-comps-n-k** (using Mathlib's Composition):
For `n > 0` and `k > 0`, the number of compositions of `n` into `k` parts is `C(n-1, k-1)`.

The proof establishes a bijection between compositions of length k and (k-1)-subsets
of `Fin (n-1)`, then uses the formula for counting subsets of a given size.
-/
lemma card_compositions_of_length (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    ((Finset.univ : Finset (_root_.Composition n)).filter (fun c => c.length = k)).card
    = Nat.choose (n - 1) (k - 1) := by
  -- Establish bijection between {c | c.length = k} and {s | s.card = k - 1}
  let f : {c : _root_.Composition n | c.length = k} →
      {s : Finset (Fin (n - 1)) | s.card = k - 1} :=
    fun ⟨c, hc⟩ => ⟨compositionToFinset n c, by
      have h := compositionToFinset_card_add_one n hn c
      rw [hc] at h
      have : (compositionToFinset n c).card = k - 1 := by omega
      exact this⟩

  have hf_bij : Function.Bijective f := by
    constructor
    · intro ⟨c1, hc1⟩ ⟨c2, hc2⟩ heq
      simp only [f, Subtype.mk.injEq] at heq
      exact Subtype.ext ((compositionToFinset n).injective heq)
    · intro ⟨s, hs⟩
      let c := (compositionToFinset n).symm s
      have h := compositionToFinset_card_add_one n hn c
      simp only [c] at h ⊢
      have heq : (compositionToFinset n) ((compositionToFinset n).symm s) = s :=
        Equiv.apply_symm_apply _ _
      rw [heq] at h
      simp only [Set.mem_ofPred_eq] at hs
      rw [hs] at h
      have hc : ((compositionToFinset n).symm s).length = k := by omega
      exact ⟨⟨(compositionToFinset n).symm s, hc⟩, by simp [f]⟩

  -- Use the bijection to count
  have h_card : Fintype.card {c : _root_.Composition n | c.length = k} =
      Fintype.card {s : Finset (Fin (n - 1)) | s.card = k - 1} :=
    Fintype.card_of_bijective hf_bij

  -- Convert to Finset.card
  rw [show ((Finset.univ : Finset (_root_.Composition n)).filter
      (fun c => c.length = k)).card =
      Fintype.card {c : _root_.Composition n | c.length = k} from by
        simp [Fintype.card_subtype]]
  rw [h_card]

  -- Use powersetCard formula
  have h_powerset : Fintype.card {s : Finset (Fin (n - 1)) | s.card = k - 1} =
      (powersetCard (k - 1) (Finset.univ : Finset (Fin (n - 1)))).card := by
    simp only [Fintype.card_subtype]
    congr 1
    ext s
    simp [powersetCard]

  rw [h_powerset, card_powersetCard, Finset.card_univ, Fintype.card_fin]

end MathlibComposition

namespace Composition

/--
**Theorem thm.fps.comps.num-comps-n-k**:
For `n > 0` and `k > 0`, the number of compositions of `n` into `k` parts is `Nat.choose (n-1) (k-1)`.

Note: The source text states this as `C(n-1, n-k) = C(n-1, k-1)` for `n > 0`, but
`C(n-1, n-k)` uses integer binomial coefficients where `C(-1, -k) = 0` for `k > 0`.
In Lean's `Nat.choose` with truncating subtraction, `Nat.choose (0-1) (0-k) = Nat.choose 0 0 = 1`,
which is incorrect for the case `n = 0, k > 0`. Additionally, when `n > 0` and `k = 0`,
the formula `Nat.choose (n-1) (k-1) = Nat.choose (n-1) 0 = 1`, but there are no compositions
of `n > 0` into 0 parts (the count should be 0).

Therefore, we require both `n > 0` and `k > 0`, and handle edge cases separately.
-/
lemma card_ofSizeIntoParts_pos (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    Fintype.card (ofSizeIntoParts n k) = Nat.choose (n - 1) (k - 1) := by
  -- Use the equivalence with Mathlib's filtered compositions
  rw [Fintype.card_congr (equivMathlibFiltered n k)]
  -- Convert to Finset.card form
  rw [show Fintype.card {c : _root_.Composition n | c.length = k} =
      ((Finset.univ : Finset (_root_.Composition n)).filter (fun c => c.length = k)).card from by
        simp [Fintype.card_subtype]]
  -- Use the existing theorem from MathlibComposition namespace
  exact MathlibComposition.card_compositions_of_length n k hn hk

/--
For `n > 0` and `k = 0`, there are no compositions (since compositions have positive parts,
and the sum of zero positive integers is 0, not `n`).
-/
lemma card_ofSizeIntoParts_k_zero (n : ℕ) (hn : 0 < n) :
    Fintype.card (ofSizeIntoParts n 0) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro ⟨α, hsize, hlen⟩
  simp only [len] at hlen
  simp only [size] at hsize
  have hα : α = [] := List.eq_nil_of_length_eq_zero hlen
  simp [hα] at hsize
  omega

/--
For `n = 0`, the only composition is the empty one (into 0 parts).
There are no compositions of 0 into k > 0 parts (since all parts must be positive).
-/
lemma card_ofSizeIntoParts_zero (k : ℕ) :
    Fintype.card (ofSizeIntoParts 0 k) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · -- k = 0: the only composition is the empty list
    subst hk
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨[], ?_⟩, ?_⟩
    · constructor <;> rfl
    · intro ⟨α, hα⟩
      apply Subtype.ext
      exact empty_of_size_zero α hα.1
  · -- k > 0: there are no compositions
    apply Fintype.card_eq_zero_iff.mpr
    constructor
    intro ⟨α, hα⟩
    have h1 := empty_of_size_zero α hα.1
    simp only [len, h1, List.length_nil] at hα
    exact hk hα.2.symm

/--
**Theorem thm.fps.comps.num-comps-n**:
The number of compositions of `n` is `2^(n-1)` when `n > 0`, and `1` when `n = 0`.

This is proved by establishing an equivalence with Mathlib's `Composition n` and using
`composition_card` from Mathlib.
-/
lemma card_ofSize (n : ℕ) :
    Fintype.card (ofSize n) = if n = 0 then 1 else 2 ^ (n - 1) := by
  rw [Fintype.card_congr (equivMathlib n)]
  rw [composition_card]
  rcases n with _ | n
  · simp
  · simp

/--
For `n > 0`, the number of compositions of `n` is `2^(n-1)`.
-/
lemma card_ofSize_pos (n : ℕ) (hn : 0 < n) :
    Fintype.card (ofSize n) = 2 ^ (n - 1) := by
  rw [card_ofSize]
  simp [Nat.pos_iff_ne_zero.mp hn]

end Composition

namespace WeakComposition


/-- The size of the empty weak composition is 0. -/
@[simp]
lemma size_nil : size ([] : WeakComposition) = 0 := rfl

/-- The length of the empty weak composition is 0. -/
@[simp]
lemma len_nil : len ([] : WeakComposition) = 0 := rfl

/-- The size of a cons weak composition is the head value plus the tail size. -/
@[simp]
lemma size_cons (a : ℕ) (α : WeakComposition) : size (a :: α) = a + size α := rfl

/-- The length of a cons weak composition is the tail length plus 1. -/
@[simp]
lemma len_cons (a : ℕ) (α : WeakComposition) : len (a :: α) = len α + 1 := rfl

namespace ofSizeIntoParts'

/--
**Theorem thm.fps.comps.num-wcomps-n-k**:
The number of weak compositions of `n` into `k` parts is `Nat.choose (n+k-1) n`.

The proof uses the "stars and bars" technique: weak compositions of `n` into `k` parts
are in bijection with multisets of size `n` from an alphabet of size `k` (i.e., `Sym (Fin k) n`),
which are counted by `Nat.choose (n+k-1) n`.
-/
lemma card_eq (n k : ℕ) : Fintype.card (ofSizeIntoParts' n k) = Nat.choose (n + k - 1) n := by
  rw [Fintype.card_congr (equivSym n k)]
  cases k with
  | zero =>
    simp only [Nat.add_zero]
    cases n with
    | zero => simp
    | succ n => simp
  | succ k =>
    rw [Sym.card_sym_eq_choose]
    congr 1
    simp only [Fintype.card_fin]
    omega

end ofSizeIntoParts'

/--
**Theorem thm.fps.comps.num-wcomps-n-k** (first form):
The number of weak compositions of `n` into `k` parts is `Nat.choose (n+k-1) n`.
-/
lemma card_ofSizeIntoParts (n k : ℕ) :
    Fintype.card (ofSizeIntoParts n k) = Nat.choose (n + k - 1) n := by
  rw [Fintype.card_congr (ofSizeIntoParts_equiv n k)]
  exact ofSizeIntoParts'.card_eq n k

/--
Alternative form: for `k > 0`, the number of weak compositions of `n` into `k` parts
is `Nat.choose (n+k-1) (k-1)`.
-/
lemma card_ofSizeIntoParts_pos (n k : ℕ) (hk : 0 < k) :
    Fintype.card (ofSizeIntoParts n k) = Nat.choose (n + k - 1) (k - 1) := by
  rw [card_ofSizeIntoParts]
  cases k with
  | zero => omega
  | succ k =>
    simp only [Nat.add_sub_cancel]
    rw [Nat.choose_symm_of_eq_add]
    omega

/--
For `k = 0`, the only weak composition is the empty one (which has size 0).
-/
lemma card_ofSizeIntoParts_zero (n : ℕ) :
    Fintype.card (ofSizeIntoParts n 0) = if n = 0 then 1 else 0 := by
  rw [card_ofSizeIntoParts]
  simp only [Nat.add_zero]
  cases n with
  | zero => simp
  | succ n => simp

end WeakComposition

namespace BoundedWeakComposition

end BoundedWeakComposition

/--
The cardinality of `BoundedWeakComposition n k 2` (binary k-strings with n ones) is `C(k, n)`.
This is because choosing a binary string with n ones is equivalent to choosing which n
of the k positions will be 1.
-/
lemma card_boundedWeakComposition_2 (k n : ℕ) :
    Fintype.card (BoundedWeakComposition n k 2) = Nat.choose k n := by
  rw [Fintype.card_congr (binaryStringEquiv k n)]
  simp only [Fintype.card_subtype, Finset.card_filter]
  have h1 : ∑ i : Finset (Fin k), (if i.card = n then 1 else 0) =
      (Finset.powersetCard n (Finset.univ : Finset (Fin k))).card := by
    rw [← Finset.card_filter]
    congr 1
    ext s
    simp [Finset.mem_powersetCard]
  rw [h1, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/--
**Proposition prop.fps.comps.num-w2comps-n-k-id**:
For `n, k ∈ ℕ`, we have
`C(k, n) = ∑_{j : 2*j ≤ n} (-1)^j * C(k,j) * C(n - 2j + k - 1, n - 2j)`.

This identity arises from the special case `p = 2` of Theorem thm.fps.comps.num-wpcomps-n-k,
where we count binary strings (k-tuples of 0s and 1s) with exactly n ones.

## Proof Strategy

The proof uses generating functions:
1. Binary k-strings with n ones are counted by `C(k, n)` (choosing which n positions are 1s)
2. By Theorem thm.fps.comps.num-wpcomps-n-k with `p = 2`, the count also equals the sum formula
3. The generating function identity `(1+X)^k = (1-X²)^k / (1-X)^k` underlies this:
   - `(1-X²) = (1-X)(1+X)`, so `(1-X²)^k / (1-X)^k = (1+X)^k`
   - Coefficient of X^n in `(1+X)^k` is `C(k, n)`
   - Coefficient of X^n in `(1-X²)^k * (1-X)^{-k}` gives the sum formula via convolution

Note: The sum is restricted to `j` with `2 * j ≤ n` because when `2j > n`, the term
contributes 0 (no valid compositions exist with negative sum).
-/
lemma binom_sum_identity (n k : ℕ) :
    (Nat.choose k n : ℤ) =
      ∑ j ∈ (range (k + 1)).filter (fun j => 2 * j ≤ n),
        (-1 : ℤ) ^ j * (Nat.choose k j) * (Nat.choose (n - 2 * j + k - 1) (n - 2 * j)) := by
  -- The proof combines two facts:
  -- 1. card_boundedWeakComposition_2: |BoundedWeakComposition n k 2| = C(k, n)
  -- 2. BoundedWeakComposition.card: |BoundedWeakComposition n k 2| = RHS (via inclusion-exclusion)
  rw [← card_boundedWeakComposition_2 k n]
  exact BoundedWeakComposition.card n k 2

end AlgebraicCombinatorics
end


/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_size_ge_len_le
-- given
  (α : AlgebraicCombinatorics.Composition) :
-- imply
  AlgebraicCombinatorics.Composition.len α
    ≤ AlgebraicCombinatorics.Composition.size α := by
-- proof
  apply AlgebraicCombinatorics.Composition.size_ge_len α

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_size_singleton_eq
-- given
  (n : PNat) :
-- imply
  AlgebraicCombinatorics.Composition.size
    (AlgebraicCombinatorics.Composition.singleton n) = n.val := by
-- proof
  apply AlgebraicCombinatorics.Composition.size_singleton n

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_len_singleton_eq
-- given
  (n : PNat) :
-- imply
  AlgebraicCombinatorics.Composition.len
    (AlgebraicCombinatorics.Composition.singleton n) = 1 := by
-- proof
  apply AlgebraicCombinatorics.Composition.len_singleton n

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_size_append_eq
-- given
  (α β : AlgebraicCombinatorics.Composition) :
-- imply
  AlgebraicCombinatorics.Composition.size (α ++ β) =
    AlgebraicCombinatorics.Composition.size α +
      AlgebraicCombinatorics.Composition.size β := by
-- proof
  apply AlgebraicCombinatorics.Composition.size_append α β

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_len_append_eq
-- given
  (α β : AlgebraicCombinatorics.Composition) :
-- imply
  AlgebraicCombinatorics.Composition.len (α ++ β) =
    AlgebraicCombinatorics.Composition.len α +
      AlgebraicCombinatorics.Composition.len β := by
-- proof
  apply AlgebraicCombinatorics.Composition.len_append α β

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_to_blocks_of_blocks_eq
-- given
  (blocks : List ℕ) (hpos : ∀ {i}, i ∈ blocks → 0 < i) :
-- imply
  AlgebraicCombinatorics.Composition.toBlocks
    (AlgebraicCombinatorics.Composition.ofBlocks blocks hpos) = blocks := by
-- proof
  apply AlgebraicCombinatorics.Composition.toBlocks_ofBlocks blocks hpos

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_of_blocks_to_blocks_eq
-- given
  (α : AlgebraicCombinatorics.Composition) :
-- imply
  AlgebraicCombinatorics.Composition.ofBlocks
    (AlgebraicCombinatorics.Composition.toBlocks α)
    (fun hi => by
      simp only [AlgebraicCombinatorics.Composition.toBlocks, List.mem_map] at hi
      obtain ⟨x, _, rfl⟩ := hi
      exact x.2) = α := by
-- proof
  apply AlgebraicCombinatorics.Composition.ofBlocks_toBlocks α

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_size_eq_sum_to_blocks_eq
-- given
  (α : AlgebraicCombinatorics.Composition) :
-- imply
  AlgebraicCombinatorics.Composition.size α =
    (AlgebraicCombinatorics.Composition.toBlocks α).sum := by
-- proof
  apply AlgebraicCombinatorics.Composition.size_eq_sum_toBlocks α

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_len_eq_to_blocks_length_eq
-- given
  (α : AlgebraicCombinatorics.Composition) :
-- imply
  AlgebraicCombinatorics.Composition.len α =
    (AlgebraicCombinatorics.Composition.toBlocks α).length := by
-- proof
  apply AlgebraicCombinatorics.Composition.len_eq_toBlocks_length α

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_card_of_size_into_parts_pos_eq
-- given
  (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
-- imply
  Fintype.card (AlgebraicCombinatorics.Composition.ofSizeIntoParts n k) =
    Nat.choose (n - 1) (k - 1) := by
-- proof
  apply AlgebraicCombinatorics.Composition.card_ofSizeIntoParts_pos n k hn hk

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_card_of_size_into_parts_k_zero_eq
-- given
  (n : ℕ) (hn : 0 < n) :
-- imply
  Fintype.card (AlgebraicCombinatorics.Composition.ofSizeIntoParts n 0) = 0 := by
-- proof
  apply AlgebraicCombinatorics.Composition.card_ofSizeIntoParts_k_zero n hn

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_card_of_size_into_parts_zero_eq
-- given
  (k : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.Composition.ofSizeIntoParts 0 k) =
    if k = 0 then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.Composition.card_ofSizeIntoParts_zero k

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_card_of_size_eq
-- given
  (n : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.Composition.ofSize n) =
    if n = 0 then 1 else 2 ^ (n - 1) := by
-- proof
  apply AlgebraicCombinatorics.Composition.card_ofSize n

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_card_of_size_pos_eq
-- given
  (n : ℕ) (hn : 0 < n) :
-- imply
  Fintype.card (AlgebraicCombinatorics.Composition.ofSize n) = 2 ^ (n - 1) := by
-- proof
  apply AlgebraicCombinatorics.Composition.card_ofSize_pos n hn

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma mathlib_composition_card_compositions_of_length_eq
-- given
  (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
-- imply
  ((Finset.univ : Finset (_root_.Composition n)).filter
    (fun c => c.length = k)).card = Nat.choose (n - 1) (k - 1) := by
-- proof
  apply AlgebraicCombinatorics.MathlibComposition.card_compositions_of_length n k hn hk

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma weak_composition_card_of_size_into_parts_eq
-- given
  (n k : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.WeakComposition.ofSizeIntoParts n k) =
    Nat.choose (n + k - 1) n := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.card_ofSizeIntoParts n k

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma weak_composition_card_of_size_into_parts_pos_eq
-- given
  (n k : ℕ) (hk : 0 < k) :
-- imply
  Fintype.card (AlgebraicCombinatorics.WeakComposition.ofSizeIntoParts n k) =
    Nat.choose (n + k - 1) (k - 1) := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.card_ofSizeIntoParts_pos n k hk

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma weak_composition_card_of_size_into_parts_zero_eq
-- given
  (n : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.WeakComposition.ofSizeIntoParts n 0) =
    if n = 0 then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.card_ofSizeIntoParts_zero n

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma weak_composition_of_size_into_parts_ext_eq
-- given
  {n k : ℕ} {x y : AlgebraicCombinatorics.WeakComposition.ofSizeIntoParts' n k}
  (h : x.val = y.val) :
-- imply
  x = y := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.ofSizeIntoParts'.ext h

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma bounded_weak_composition_card_eq
-- given
  (n k p : ℕ) :
-- imply
  (Fintype.card (AlgebraicCombinatorics.BoundedWeakComposition n k p) : ℤ) =
    ∑ j ∈ (range (k + 1)).filter (fun j => p * j ≤ n),
      (-1 : ℤ) ^ j * (Nat.choose k j) *
        (Nat.choose (n - p * j + k - 1) (n - p * j)) := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.card n k p

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma card_bounded_weak_composition_2_eq
-- given
  (k n : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.BoundedWeakComposition n k 2) =
    Nat.choose k n := by
-- proof
  apply AlgebraicCombinatorics.card_boundedWeakComposition_2 k n

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma binom_sum_identity_eq
-- given
  (n k : ℕ) :
-- imply
  (Nat.choose k n : ℤ) =
    ∑ j ∈ (range (k + 1)).filter (fun j => 2 * j ≤ n),
      (-1 : ℤ) ^ j * (Nat.choose k j) *
        (Nat.choose (n - 2 * j + k - 1) (n - 2 * j)) := by
-- proof
  apply AlgebraicCombinatorics.binom_sum_identity n k

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_size_nil :
-- imply
  AlgebraicCombinatorics.Composition.size ([] : AlgebraicCombinatorics.Composition) = 0 := by
-- proof
  apply AlgebraicCombinatorics.Composition.size_nil

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_len_nil :
-- imply
  AlgebraicCombinatorics.Composition.len ([] : AlgebraicCombinatorics.Composition) = 0 := by
-- proof
  apply AlgebraicCombinatorics.Composition.len_nil

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_size_cons
-- given
  (a : PNat)
  (α : AlgebraicCombinatorics.Composition) :
-- imply
  AlgebraicCombinatorics.Composition.size (a :: α) = a.val + AlgebraicCombinatorics.Composition.size α := by
-- proof
  apply AlgebraicCombinatorics.Composition.size_cons a α

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_len_cons
-- given
  (a : PNat)
  (α : AlgebraicCombinatorics.Composition) :
-- imply
  AlgebraicCombinatorics.Composition.len (a :: α) = AlgebraicCombinatorics.Composition.len α + 1 := by
-- proof
  apply AlgebraicCombinatorics.Composition.len_cons a α

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_empty_of_size_zero
-- given
  (α : AlgebraicCombinatorics.Composition)
  (h : AlgebraicCombinatorics.Composition.size α = 0) :
-- imply
  α = [] := by
-- proof
  apply AlgebraicCombinatorics.Composition.empty_of_size_zero α h

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_compositionAsSetEquiv_card_eq_length_sub_one
-- given
  (n : ℕ)
  (hn : 0 < n)
  (c : CompositionAsSet n) :
-- imply
  (compositionAsSetEquiv n c).card + 1 = c.length := by
-- proof
  apply AlgebraicCombinatorics.MathlibComposition.compositionAsSetEquiv_card_eq_length_sub_one n hn c

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_compositionToFinset_card_add_one
-- given
  (n : ℕ)
  (hn : 0 < n)
  (c : _root_.Composition n) :
-- imply
  (AlgebraicCombinatorics.MathlibComposition.compositionToFinset n c).card + 1 = c.length := by
-- proof
  apply AlgebraicCombinatorics.MathlibComposition.compositionToFinset_card_add_one n hn c

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_size_nil_29 :
-- imply
  AlgebraicCombinatorics.WeakComposition.size ([] : AlgebraicCombinatorics.WeakComposition) = 0 := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.size_nil

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_len_nil_30 :
-- imply
  AlgebraicCombinatorics.WeakComposition.len ([] : AlgebraicCombinatorics.WeakComposition) = 0 := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.len_nil

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_size_cons_31
-- given
  (a : ℕ)
  (α : AlgebraicCombinatorics.WeakComposition) :
-- imply
  AlgebraicCombinatorics.WeakComposition.size (a :: α) = a + AlgebraicCombinatorics.WeakComposition.size α := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.size_cons a α

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_len_cons_32
-- given
  (a : ℕ)
  (α : AlgebraicCombinatorics.WeakComposition) :
-- imply
  AlgebraicCombinatorics.WeakComposition.len (a :: α) = AlgebraicCombinatorics.WeakComposition.len α + 1 := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.len_cons a α

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_sum_count_eq_card
-- given
  (k : ℕ)
  (m : Multiset (Fin k)) :
-- imply
  ∑ i : Fin k, m.count i = m.card := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.ofSizeIntoParts'.sum_count_eq_card k m

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_ofFun_length
  {k : ℕ}
-- given
  (f : Fin k → ℕ) :
-- imply
  (AlgebraicCombinatorics.WeakComposition.ofFun f).length = k := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.ofFun_length f

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_ofFun_get
  {k : ℕ}
-- given
  (f : Fin k → ℕ)
  (i : Fin k) :
-- imply
  (AlgebraicCombinatorics.WeakComposition.ofFun f).get (i.cast (AlgebraicCombinatorics.WeakComposition.ofFun_length f).symm) = f i := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.ofFun_get f i

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_ofFun_sum
  {k : ℕ}
-- given
  (f : Fin k → ℕ) :
-- imply
  (AlgebraicCombinatorics.WeakComposition.ofFun f).sum = ∑ i, f i := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.ofFun_sum f

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_toFun_ofFun
  {k : ℕ}
-- given
  (f : Fin k → ℕ) :
-- imply
  AlgebraicCombinatorics.WeakComposition.toFun (AlgebraicCombinatorics.WeakComposition.ofFun f) k (AlgebraicCombinatorics.WeakComposition.ofFun_length f) = f := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.toFun_ofFun f

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_list_sum_eq_finset_sum
-- given
  (l : List ℕ) :
-- imply
  l.sum = ∑ i : Fin l.length, l.get i := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.list_sum_eq_finset_sum l

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_ofFun_toFun
-- given
  (α : AlgebraicCombinatorics.WeakComposition)
  (k : ℕ)
  (hlen : AlgebraicCombinatorics.WeakComposition.len α = k) :
-- imply
  AlgebraicCombinatorics.WeakComposition.ofFun (AlgebraicCombinatorics.WeakComposition.toFun α k hlen) = α := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.ofFun_toFun α k hlen

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_geom_series_mul_one_sub
-- given
  (p : ℕ) :
-- imply
  (∑ i ∈ range p, (PowerSeries.X : PowerSeries ℤ) ^ i) * (1 - PowerSeries.X) = 1 - PowerSeries.X ^ p := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.geom_series_mul_one_sub p

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_invOneSubPow_pow
-- given
  (k : ℕ) :
-- imply
  (PowerSeries.invOneSubPow ℤ 1) ^ k = PowerSeries.invOneSubPow ℤ k := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.invOneSubPow_pow k

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_geom_series_eq_mul_inv
-- given
  (p : ℕ) :
-- imply
  (∑ i ∈ range p, (PowerSeries.X : PowerSeries ℤ) ^ i) = (1 - PowerSeries.X ^ p) * (PowerSeries.invOneSubPow ℤ 1).val := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.geom_series_eq_mul_inv p

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_genFun_eq
-- given
  (k p : ℕ) :
-- imply
  AlgebraicCombinatorics.BoundedWeakComposition.genFun k p = (1 - PowerSeries.X ^ p) ^ k * (PowerSeries.invOneSubPow ℤ k).val := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.genFun_eq k p

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_coeff_invOneSubPow
-- given
  (k n : ℕ)
  (hk : 0 < k) :
-- imply
  (PowerSeries.invOneSubPow ℤ k).val.coeff n = Nat.choose (k - 1 + n) (k - 1) := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.coeff_invOneSubPow k n hk

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_coeff_genFun
-- given
  (n k p : ℕ) :
-- imply
  (AlgebraicCombinatorics.BoundedWeakComposition.genFun k p).coeff n = Fintype.card (AlgebraicCombinatorics.BoundedWeakComposition n k p) := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.coeff_genFun n k p

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_coeff_genFun_formula
-- given
  (n k p : ℕ) :
-- imply
  (AlgebraicCombinatorics.BoundedWeakComposition.genFun k p).coeff n = ∑ j ∈ (range (k + 1)).filter (fun j => p * j ≤ n), (-1 : ℤ) ^ j * (Nat.choose k j) * (Nat.choose (n - p * j + k - 1) (n - p * j)) := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.coeff_genFun_formula n k p

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma x_ofSizeIntoParts'_card_eq
-- given
  (n k : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.WeakComposition.ofSizeIntoParts' n k) = Nat.choose (n + k - 1) n := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.ofSizeIntoParts'.card_eq n k

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma pv_count_sum_replicate
-- given
  (k : ℕ)
  (f : Fin k → ℕ)
  (i : Fin k) :
-- imply
  Multiset.count i (∑ j : Fin k, Multiset.replicate (f j) j) = f i := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.ofSizeIntoParts'.count_sum_replicate k f i

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma pv_sum_map_add_one
-- given
  (lst : List ℕ) :
-- imply
  (lst.map (fun a => a + 1)).sum = lst.sum + lst.length := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.sum_map_add_one lst

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma pv_pnat_list_sum_ge_length
-- given
  (lst : List PNat) :
-- imply
  (lst.map (·.val)).sum ≥ lst.length := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.pnat_list_sum_ge_length lst

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma pv_sum_map_sub_one
-- given
  (lst : List PNat) :
-- imply
  (lst.map (fun b : PNat => b.val - 1)).sum = (lst.map (·.val)).sum - lst.length := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.sum_map_sub_one lst

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma pv_coeff_geom_series
-- given
  (p m : ℕ) :
-- imply
  (∑ i ∈ range p, (PowerSeries.X : PowerSeries ℤ) ^ i).coeff m = if m < p then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.coeff_geom_series p m

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma pv_sum_range_eq_sum_fin
-- given
  (k : ℕ)
  (l : Finsupp ℕ ℕ) :
-- imply
  ∑ i ∈ range k, l i = ∑ i : Fin k, l i.val := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.sum_range_eq_sum_fin k l

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma pv_bwc_left_inv
-- given
  (n k p : ℕ)
  (α : BoundedWeakComposition n k p) :
-- imply
  antidiagToBwc n k p (bwcToAntidiag n k p α) = α := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.bwc_left_inv n k p α

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma pv_bwc_right_inv
-- given
  (n k p : ℕ)
  (l : boundedAntidiag n k p) :
-- imply
  bwcToAntidiag n k p (antidiagToBwc n k p l) = l := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.bwc_right_inv n k p l

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma pv_card_boundedAntidiag_eq
-- given
  (n k p : ℕ) :
-- imply
  (boundedAntidiag n k p).card = Fintype.card (BoundedWeakComposition n k p) := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.card_boundedAntidiag_eq n k p

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma pv_one_sub_X_pow_pow_eq
-- given
  (p k : ℕ) :
-- imply
  (1 - (PowerSeries.X : PowerSeries ℤ) ^ p) ^ k = ∑ j ∈ range (k + 1), PowerSeries.C ((-1 : ℤ) ^ j * (Nat.choose k j : ℤ)) * (PowerSeries.X : PowerSeries ℤ) ^ (p * j) := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.one_sub_X_pow_pow_eq p k

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma pv_coeff_one_sub_X_pow_pow
-- given
  (p k n : ℕ) :
-- imply
  PowerSeries.coeff (R := ℤ) n ((1 - PowerSeries.X ^ p) ^ k) = ∑ j ∈ (range (k + 1)).filter (fun j => p * j = n), (-1 : ℤ) ^ j * (Nat.choose k j : ℤ) := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.coeff_one_sub_X_pow_pow p k n

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma pv_choose_symm_helper
-- given
  (n k : ℕ)
  (hk : 0 < k) :
-- imply
  (k - 1 + n).choose (k - 1) = (n + k - 1).choose n := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.choose_symm_helper n k hk

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma pv_sum_fin2_eq_card_support
-- given
  (k : ℕ)
  (f : Fin k → Fin 2) :
-- imply
  ∑ i, (f i).val = (Finset.univ.filter (fun i => f i = 1)).card := by
-- proof
  apply AlgebraicCombinatorics.sum_fin2_eq_card_support k f

/--
[IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean)
-/
@[path]
private lemma pv_fin2_eq_zero_or_one
-- given
  (x : Fin 2) :
-- imply
  x = 0 ∨ x = 1 := by
-- proof
  apply AlgebraicCombinatorics.fin2_eq_zero_or_one x


-- created on 2026-10-11
-- updated on 2026-10-26
