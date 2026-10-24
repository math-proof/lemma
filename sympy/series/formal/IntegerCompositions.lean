/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
/-!
# Integer Compositions

This file formalizes integer compositions and weak compositions, following
Section sec.fps.intcomps of the source text.

## Main definitions

* `Composition` - A composition as a `List ℕ+` (tuple of positive integers)
* `Composition.append` - Concatenation of two compositions
* `Composition.ofSize n` - The subtype of compositions with size `n`
* `Composition.ofSizeIntoParts n k` - The subtype of compositions with size `n` and length `k`
* `WeakComposition` - A weak composition as a `List ℕ` (tuple of nonnegative integers)
* `WeakComposition.ofSizeIntoParts n k` - Weak compositions of `n` into `k` parts
* `BoundedWeakComposition n k p` - Weak compositions with entries in `{0, 1, ..., p-1}`

## Main results

* `Composition.card_ofSizeIntoParts_pos` - The number of compositions of `n` into `k` parts
  is `Nat.choose (n-1) (k-1)` for `n > 0` and `k > 0` (Theorem thm.fps.comps.num-comps-n-k)
* `Composition.card_ofSizeIntoParts_zero` - The number of compositions of `0` into `k` parts
  is `1` if `k = 0`, else `0`
* `Composition.card_ofSizeIntoParts_k_zero` - The number of compositions of `n > 0` into
  `0` parts is `0`
* `Composition.card_ofSize` - The number of compositions of `n` is `2^(n-1)` for `n > 0`
  (Theorem thm.fps.comps.num-comps-n)
* `WeakComposition.card_ofSizeIntoParts` - The number of weak compositions of `n` into `k` parts
  is `Nat.choose (n+k-1) n` (Theorem thm.fps.comps.num-wcomps-n-k)
* `BoundedWeakComposition.card` - The number of weak compositions with bounded entries
  (Theorem thm.fps.comps.num-wpcomps-n-k)
* `binom_sum_identity` - An identity involving binomial coefficients
  (Proposition prop.fps.comps.num-w2comps-n-k-id)

## Implementation notes

This file defines `Composition` as `List ℕ+`, which is an alternative representation to
Mathlib's `Mathlib.Combinatorics.Enumerative.Composition` which uses `Composition n` as a
structure with `blocks : List ℕ` and proofs of positivity and sum. Both representations
are equivalent; we use `List ℕ+` here to follow the source text's presentation more directly.

## References

See the source LaTeX file `AlgebraicCombinatorics/tex/FPS/IntegerCompositions.tex`
-/


open Finset Nat BigOperators
set_option allowUnsafeReducibility true
attribute [local reducible] PNat

namespace AlgebraicCombinatorics
/-! ### Integer Compositions -/


/--
An integer composition is a finite tuple of positive integers.
We represent it as a list of positive integers.

(Definition def.fps.comps, part (a))
-/
abbrev Composition := List ℕ+

namespace Composition

instance : Inhabited Composition := ⟨[]⟩

/--
The size of a composition is the sum of its entries.

(Definition def.fps.comps, part (b))
-/
def size (α : Composition) : ℕ := (α.map (·.val)).sum

/--
The length of a composition is the number of parts.
(We use `len` to avoid conflict with `List.length`.)

(Definition def.fps.comps, part (c))
-/
def len (α : Composition) : ℕ := α.length
/-! #### Basic `@[simp]` lemmas for `size` and `len` -/
/-! #### Singleton constructor -/


/-- A composition with a single part. -/
def singleton (n : ℕ+) : Composition := [n]
/-! #### Append operation -/


/-- Concatenation of two compositions. -/
def append (α β : Composition) : Composition := List.append α β

instance : Append Composition := ⟨append⟩

/--
A composition of `n` is a composition whose size is `n`.

(Definition def.fps.comps, part (d))
-/
def ofSize (n : ℕ) : Type := { α : Composition // α.size = n }

/--
A composition of `n` into `k` parts is a composition with size `n` and length `k`.

(Definition def.fps.comps, part (e))
-/
def ofSizeIntoParts (n k : ℕ) : Type :=
  { α : Composition // α.size = n ∧ α.len = k }

-- Example: (3, 8, 6) is a composition of 17 into 3 parts
-- (Example exa.fps.comps.1)
example : ofSizeIntoParts 17 3 :=
  ⟨[⟨3, by omega⟩, ⟨8, by omega⟩, ⟨6, by omega⟩],
   by simp only [size, List.map, List.sum_cons, List.sum_nil]; rfl,
   rfl⟩

-- The empty tuple is the only composition of 0
example : ofSize 0 := ⟨[], by simp [size]⟩
/-! #### Equivalence with Mathlib's Composition type -/


/-- Convert a composition (List ℕ+) to a blocks list (List ℕ) -/
def toBlocks (α : Composition) : List ℕ := α.map (·.val)

/-- Convert a blocks list with positivity proof to a composition (List ℕ+) -/
def ofBlocks (blocks : List ℕ) (hpos : ∀ {i}, i ∈ blocks → 0 < i) : Composition :=
  blocks.pmap (fun i (hi : 0 < i) => ⟨i, hi⟩) (fun _ ha => hpos ha)

theorem toBlocks_ofBlocks (blocks : List ℕ) (hpos : ∀ {i}, i ∈ blocks → 0 < i) :
    toBlocks (ofBlocks blocks hpos) = blocks := by
  simp only [toBlocks, ofBlocks]
  induction blocks with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.pmap_cons, List.map_cons]
    congr 1
    exact ih (fun hi => hpos (List.mem_cons_of_mem x hi))

theorem ofBlocks_toBlocks (α : Composition) :
    ofBlocks (toBlocks α) (fun hi => by
      simp only [toBlocks, List.mem_map] at hi
      obtain ⟨x, _, rfl⟩ := hi
      exact x.2) = α := by
  simp only [toBlocks, ofBlocks]
  induction α with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.pmap_cons]
    rw [List.cons.injEq]
    exact ⟨rfl, ih⟩

theorem size_eq_sum_toBlocks (α : Composition) : α.size = (toBlocks α).sum := rfl

theorem len_eq_toBlocks_length (α : Composition) : α.len = (toBlocks α).length := by
  simp [len, toBlocks]

/--
Equivalence between our `Composition.ofSize n` and Mathlib's `Composition n`.
This allows us to use Mathlib's `composition_card` theorem.
-/
def equivMathlib (n : ℕ) : Composition.ofSize n ≃ _root_.Composition n where
  toFun := fun ⟨α, hα⟩ => {
    blocks := toBlocks α
    blocks_pos := fun hi => by
      simp only [toBlocks, List.mem_map] at hi
      obtain ⟨x, _, rfl⟩ := hi
      exact x.2
    blocks_sum := hα
  }
  invFun := fun c => ⟨ofBlocks c.blocks c.blocks_pos, by
    simp only [size_eq_sum_toBlocks, toBlocks_ofBlocks]
    exact c.blocks_sum⟩
  left_inv := fun ⟨α, hα⟩ => by
    simp only
    congr 1
    exact ofBlocks_toBlocks α
  right_inv := fun c => by
    simp only [_root_.Composition.ext_iff]
    exact toBlocks_ofBlocks c.blocks c.blocks_pos

/--
Equivalence between `Composition.ofSizeIntoParts n k` and the filtered set of Mathlib compositions
of `n` with length `k`.
-/
def equivMathlibFiltered (n k : ℕ) :
    Composition.ofSizeIntoParts n k ≃ {c : _root_.Composition n | c.length = k} where
  toFun := fun ⟨α, hα⟩ => ⟨{
    blocks := toBlocks α
    blocks_pos := fun hi => by
      simp only [toBlocks, List.mem_map] at hi
      obtain ⟨x, _, rfl⟩ := hi
      exact x.2
    blocks_sum := hα.1
  }, by
    simp only [Set.mem_ofPred_eq, _root_.Composition.length]
    rw [← len_eq_toBlocks_length]
    exact hα.2⟩
  invFun := fun ⟨c, hc⟩ => ⟨ofBlocks c.blocks c.blocks_pos, by
    simp only [size_eq_sum_toBlocks, toBlocks_ofBlocks]
    refine ⟨c.blocks_sum, ?_⟩
    simp only [len, ofBlocks, List.length_pmap]
    exact hc⟩
  left_inv := fun ⟨α, hα⟩ => by
    simp only
    congr 1
    exact ofBlocks_toBlocks α
  right_inv := fun ⟨c, hc⟩ => by
    simp only
    apply Subtype.ext
    simp only [_root_.Composition.ext_iff]
    exact toBlocks_ofBlocks c.blocks c.blocks_pos

/--
The set of all compositions of `n` into `k` parts is finite.
-/
instance fintypeOfSizeIntoParts (n k : ℕ) : Fintype (ofSizeIntoParts n k) :=
  Fintype.ofEquiv _ (equivMathlibFiltered n k).symm

end Composition
/-! ### Counting Compositions via Mathlib

We prove the main counting theorem using Mathlib's `Composition n` type, which has
a well-developed API including an equivalence with subsets of `Fin (n-1)`.

The key insight is that compositions of `n` into `k` parts correspond bijectively
to `(k-1)`-element subsets of `{1, ..., n-1}`, giving the count `C(n-1, k-1)`.
-/


namespace MathlibComposition

/-- Equivalence between Mathlib's `Composition n` and subsets of `Fin (n-1)`. -/
def compositionToFinset (n : ℕ) : _root_.Composition n ≃ Finset (Fin (n - 1)) :=
  (compositionEquiv n).trans (compositionAsSetEquiv n)

end MathlibComposition

namespace Composition

/--
The set of all compositions of `n` is finite.
-/
instance fintypeOfSize (n : ℕ) : Fintype (ofSize n) :=
  Fintype.ofEquiv _ (equivMathlib n).symm

end Composition
/-! ### Weak Compositions -/


/--
A weak composition is a finite tuple of nonnegative integers.

(Definition def.fps.wcomps, part (a))
-/
abbrev WeakComposition := List ℕ

namespace WeakComposition

instance : Inhabited WeakComposition := ⟨[]⟩

/--
The size of a weak composition is the sum of its entries.

(Definition def.fps.wcomps, part (b))
-/
def size (α : WeakComposition) : ℕ := α.sum

/--
The length of a weak composition is the number of parts.
(We use `len` to avoid conflict with `List.length`.)

(Definition def.fps.wcomps, part (c))
-/
def len (α : WeakComposition) : ℕ := α.length
/-! #### Basic `@[simp]` lemmas for `size` and `len` -/

/--
A weak composition of `n` is a weak composition whose size is `n`.

(Definition def.fps.wcomps, part (d))
-/
def ofSize (n : ℕ) : Type := { α : WeakComposition // α.size = n }

/--
A weak composition of `n` into `k` parts is a tuple of `k` nonnegative integers summing to `n`.

(Definition def.fps.wcomps, part (e))
-/
def ofSizeIntoParts (n k : ℕ) : Type :=
  { α : WeakComposition // α.size = n ∧ α.len = k }

-- Example: (3, 0, 1, 2) is a weak composition of 6 into 4 parts
-- (Example exa.fps.wcomps.1)
example : ofSizeIntoParts 6 4 :=
  ⟨[3, 0, 1, 2],
   by simp only [size, List.sum_cons, List.sum_nil]; rfl,
   rfl⟩
/-! #### Function representation of weak compositions -/


/--
Alternative representation of weak compositions as functions `Fin k → ℕ`.
This is equivalent to `ofSizeIntoParts n k` but easier to work with for cardinality proofs.
-/
def ofSizeIntoParts' (n k : ℕ) : Type :=
  { f : Fin k → ℕ // ∑ i, f i = n }

namespace ofSizeIntoParts'

@[ext]
theorem ext {n k : ℕ} {x y : ofSizeIntoParts' n k} (h : x.val = y.val) : x = y :=
  Subtype.ext h

/-- Key lemma: sum of counts over a finite type equals cardinality. -/
theorem sum_count_eq_card (k : ℕ) (m : Multiset (Fin k)) :
    ∑ i : Fin k, m.count i = m.card := by
  conv_rhs => rw [← Multiset.toFinset_sum_count_eq m]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  simp only [Multiset.mem_toFinset, Multiset.count_eq_zero] at hx ⊢
  exact hx

/-- Bijection from `Sym (Fin k) n` to `ofSizeIntoParts' n k`. -/
def fromSym (n k : ℕ) : Sym (Fin k) n → ofSizeIntoParts' n k := fun s =>
  ⟨fun i => Multiset.count i s.val, by rw [sum_count_eq_card]; exact s.prop⟩

/-- Bijection from `ofSizeIntoParts' n k` to `Sym (Fin k) n`. -/
def toSym (n k : ℕ) : ofSizeIntoParts' n k → Sym (Fin k) n := fun ⟨f, hf⟩ =>
  ⟨∑ i : Fin k, Multiset.replicate (f i) i, by
    simp only [Multiset.card_sum, Multiset.card_replicate]
    exact hf⟩

/-- Helper lemma: counting in a sum of replicates. -/
theorem count_sum_replicate (k : ℕ) (f : Fin k → ℕ) (i : Fin k) :
    Multiset.count i (∑ j : Fin k, Multiset.replicate (f j) j) = f i := by
  rw [Multiset.count_sum']
  rw [Finset.sum_eq_single i]
  · simp [Multiset.count_replicate_self]
  · intro j _ hji
    simp only [Multiset.count_replicate]
    simp [hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Equivalence between `ofSizeIntoParts' n k` and `Sym (Fin k) n`. -/
def equivSym (n k : ℕ) : ofSizeIntoParts' n k ≃ Sym (Fin k) n where
  toFun := toSym n k
  invFun := fromSym n k
  left_inv := fun ⟨f, hf⟩ => by
    unfold toSym fromSym
    ext i
    exact count_sum_replicate k f i
  right_inv := fun s => by
    unfold fromSym toSym
    ext a
    simp only [Sym.coe_mk]
    exact count_sum_replicate k (fun i => Multiset.count i s.val) a

/-- Fintype instance via the equivalence with `Sym`. -/
instance fintype (n k : ℕ) : Fintype (ofSizeIntoParts' n k) :=
  Fintype.ofEquiv _ (equivSym n k).symm

end ofSizeIntoParts'
/-! #### Equivalence between list and function representations -/


/-- Convert a list-based weak composition to a function-based one. -/
def toFun (α : WeakComposition) (k : ℕ) (hlen : α.len = k) : Fin k → ℕ :=
  fun i => α.get (i.cast hlen.symm)

/-- Convert a function to a list. -/
def ofFun {k : ℕ} (f : Fin k → ℕ) : WeakComposition :=
  List.ofFn f

theorem ofFun_length {k : ℕ} (f : Fin k → ℕ) : (ofFun f).length = k := by simp [ofFun]

theorem ofFun_get {k : ℕ} (f : Fin k → ℕ) (i : Fin k) :
    (ofFun f).get (i.cast (ofFun_length f).symm) = f i := by
  simp only [ofFun, List.get_ofFn]
  rfl

theorem ofFun_sum {k : ℕ} (f : Fin k → ℕ) : (ofFun f).sum = ∑ i, f i := by
  simp only [ofFun]
  rw [List.sum_ofFn]

theorem toFun_ofFun {k : ℕ} (f : Fin k → ℕ) :
    toFun (ofFun f) k (ofFun_length f) = f := by
  ext i
  simp only [toFun, ofFun_get]

/-- The sum of a list equals the Finset sum over its indices. -/
theorem list_sum_eq_finset_sum (l : List ℕ) : l.sum = ∑ i : Fin l.length, l.get i := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [List.get_cons_zero]
    rw [ih]
    simp only [add_right_inj]
    apply Finset.sum_congr rfl
    intro i _
    simp

theorem ofFun_toFun (α : WeakComposition) (k : ℕ) (hlen : α.len = k) :
    ofFun (toFun α k hlen) = α := by
  simp only [ofFun] at *
  apply List.ext_get
  · simp only [List.length_ofFn]
    exact hlen.symm
  · intro i hi₁ hi₂
    simp only [List.get_ofFn]
    rfl

/--
The two representations (list-based and function-based) are equivalent.
The forward direction converts a list `[a₀, a₁, ..., aₖ₋₁]` to the function `i ↦ aᵢ`.
The backward direction converts a function `f : Fin k → ℕ` to the list `[f(0), f(1), ..., f(k-1)]`.
-/
def ofSizeIntoParts_equiv (n k : ℕ) : ofSizeIntoParts n k ≃ ofSizeIntoParts' n k where
  toFun := fun ⟨α, hsize, hlen⟩ => ⟨toFun α k hlen, by
    simp only [toFun, size] at *
    have h1 : (∑ i : Fin k, α.get (Fin.cast hlen.symm i)) = ∑ i : Fin α.length, α.get i := by
      apply Finset.sum_equiv (Fin.castOrderIso hlen.symm).toEquiv
      · intro i
        exact iff_of_true (Finset.mem_univ i) (Finset.mem_univ _)
      · intro i _
        rfl
    rw [h1, ← list_sum_eq_finset_sum, hsize]⟩
  invFun := fun ⟨f, hsum⟩ => ⟨ofFun f, by simp [size, ofFun_sum, hsum], by simp [len, ofFun_length]⟩
  left_inv := fun ⟨α, hsize, hlen⟩ => by
    simp only
    apply Subtype.ext
    exact ofFun_toFun α k hlen
  right_inv := fun ⟨f, hsum⟩ => by
    simp only
    apply Subtype.ext
    exact toFun_ofFun f

/--
The set of all weak compositions of `n` into `k` parts is finite.
-/
instance fintypeOfSizeIntoParts (n k : ℕ) : Fintype (ofSizeIntoParts n k) :=
  Fintype.ofEquiv _ (ofSizeIntoParts_equiv n k).symm

/-- Helper lemma: sum of list after adding 1 to each element. -/
theorem sum_map_add_one (lst : List ℕ) : 
    (lst.map (fun a => a + 1)).sum = lst.sum + lst.length := by
  induction lst with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [ih]
    ring

/-- Helper lemma: sum of PNat values is at least the length. -/
theorem pnat_list_sum_ge_length (lst : List ℕ+) : 
    (lst.map (·.val)).sum ≥ lst.length := by
  induction lst with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have : 1 ≤ h.val := h.pos
    omega

/-- Helper lemma: sum of list after subtracting 1 from each PNat element. -/
theorem sum_map_sub_one (lst : List ℕ+) : 
    (lst.map (fun b : ℕ+ => b.val - 1)).sum = (lst.map (·.val)).sum - lst.length := by
  induction lst with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hpos : 1 ≤ h.val := h.pos
    have ht_sum_ge : (t.map (·.val)).sum ≥ t.length := pnat_list_sum_ge_length t
    omega

/--
Bijection between weak compositions of `n` into `k` parts and compositions of `n+k` into `k` parts.
Adding 1 to each entry of a weak composition gives a composition.

This is the key bijection used in the proof of Theorem thm.fps.comps.num-wcomps-n-k.
-/
def toComposition (n k : ℕ) :
    ofSizeIntoParts n k ≃ Composition.ofSizeIntoParts (n + k) k where
  toFun := fun ⟨lst, hsum, hlen⟩ =>
    ⟨lst.map (fun a => ⟨a + 1, Nat.succ_pos a⟩), by
      constructor
      · -- size = n + k
        simp only [Composition.size, List.map_map, Function.comp_def, PNat.mk_coe]
        rw [sum_map_add_one]
        simp only [size] at hsum
        simp only [len] at hlen
        rw [hsum, hlen]
      · -- len = k
        simp only [Composition.len, List.length_map]
        simp only [len] at hlen
        exact hlen⟩
  invFun := fun ⟨lst, hsum, hlen⟩ =>
    ⟨lst.map (fun b => b.val - 1), by
      constructor
      · -- size = n
        simp only [size]
        rw [sum_map_sub_one]
        simp only [Composition.size] at hsum
        simp only [Composition.len] at hlen
        rw [hsum, hlen]
        omega
      · -- len = k
        simp only [len, List.length_map]
        simp only [Composition.len] at hlen
        exact hlen⟩
  left_inv := fun ⟨lst, hsum, hlen⟩ => by
    apply Subtype.ext
    simp only [List.map_map, Function.comp_def, PNat.mk_coe, Nat.add_sub_cancel]
    exact List.map_id' lst
  right_inv := fun ⟨lst, hsum, hlen⟩ => by
    apply Subtype.ext
    simp only [List.map_map, Function.comp_def]
    have h : ∀ a : ℕ+, (⟨a.val - 1 + 1, Nat.succ_pos _⟩ : ℕ+) = a := by
      intro a
      simp only [Nat.sub_add_cancel (a.pos)]
      rfl
    simp only [h]
    exact List.map_id lst

end WeakComposition
/-! ### Bounded Weak Compositions -/


/--
A weak composition of `n` into `k` parts with entries bounded by `p`
(i.e., each entry is in `{0, 1, ..., p-1}`).

This is used in Theorem thm.fps.comps.num-wpcomps-n-k.
-/
def BoundedWeakComposition (n k p : ℕ) : Type :=
  { α : Fin k → Fin p // (∑ i, (α i).val) = n }

namespace BoundedWeakComposition

/--
The set of bounded weak compositions is finite.
-/
instance fintype (n k p : ℕ) : Fintype (BoundedWeakComposition n k p) := 
  Fintype.subtype (Finset.univ.filter (fun α => (∑ i, (α i).val) = n)) (by simp)
/-! #### Generating Function Approach

The proof of Theorem thm.fps.comps.num-wpcomps-n-k uses generating functions.
The generating function for bounded weak compositions is `W_{k,p} = (∑_{i=0}^{p-1} x^i)^k`,
which equals `((1-x^p)/(1-x))^k = (1-x^p)^k * (1-x)^{-k}`.

Using binomial expansions:
- `(1-x^p)^k = ∑_{j=0}^k (-1)^j C(k,j) x^{pj}`
- `(1-x)^{-k} = ∑_{m≥0} C(m+k-1, m) x^m` (via `PowerSeries.invOneSubPow`)

Convolving these gives the formula.
-/


/-- The generating function for bounded weak compositions. -/
noncomputable def genFun (k p : ℕ) : PowerSeries ℤ :=
  (∑ i ∈ range p, (PowerSeries.X : PowerSeries ℤ) ^ i) ^ k

/-- The geometric series identity: `(∑_{i=0}^{p-1} x^i) * (1 - x) = 1 - x^p`. -/
theorem geom_series_mul_one_sub (p : ℕ) : 
    (∑ i ∈ range p, (PowerSeries.X : PowerSeries ℤ) ^ i) * (1 - PowerSeries.X) = 
    1 - PowerSeries.X ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [sum_range_succ, add_mul, ih]
    ring

/-- Power of `invOneSubPow`: `(invOneSubPow ℤ 1)^k = invOneSubPow ℤ k`. -/
theorem invOneSubPow_pow (k : ℕ) : (PowerSeries.invOneSubPow ℤ 1) ^ k = PowerSeries.invOneSubPow ℤ k := by
  induction k with
  | zero => simp [PowerSeries.invOneSubPow_zero]
  | succ k ih =>
    rw [pow_succ, ih, mul_comm, ← PowerSeries.invOneSubPow_add]
    ring_nf

/-- The geometric series equals `(1 - X^p) * (1 - X)^{-1}`. -/
theorem geom_series_eq_mul_inv (p : ℕ) : 
    (∑ i ∈ range p, (PowerSeries.X : PowerSeries ℤ) ^ i) = 
    (1 - PowerSeries.X ^ p) * (PowerSeries.invOneSubPow ℤ 1).val := by
  have h1 : (PowerSeries.invOneSubPow ℤ 1).val = PowerSeries.mk 1 := by
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
    ext n
    simp only [PowerSeries.coeff_mk, Nat.choose_zero_right, Pi.one_apply, Nat.cast_one]
  rw [h1]
  have h2 : (1 - PowerSeries.X) * PowerSeries.mk 1 = (1 : PowerSeries ℤ) := by
    rw [mul_comm]; exact PowerSeries.mk_one_mul_one_sub_eq_one ℤ
  have h3 := geom_series_mul_one_sub p
  calc ∑ i ∈ range p, (PowerSeries.X : PowerSeries ℤ) ^ i 
      = (∑ i ∈ range p, PowerSeries.X ^ i) * 1 := by ring
    _ = (∑ i ∈ range p, PowerSeries.X ^ i) * ((1 - PowerSeries.X) * PowerSeries.mk 1) := by rw [h2]
    _ = ((∑ i ∈ range p, PowerSeries.X ^ i) * (1 - PowerSeries.X)) * PowerSeries.mk 1 := by ring
    _ = (1 - PowerSeries.X ^ p) * PowerSeries.mk 1 := by rw [h3]

/-- The generating function equals `(1-X^p)^k * (1-X)^{-k}`. -/
theorem genFun_eq (k p : ℕ) :
    genFun k p = (1 - PowerSeries.X ^ p) ^ k * (PowerSeries.invOneSubPow ℤ k).val := by
  unfold genFun
  rw [geom_series_eq_mul_inv]
  rw [mul_pow]
  congr 1
  have h1 : (PowerSeries.invOneSubPow ℤ 1).val ^ k = ((PowerSeries.invOneSubPow ℤ 1) ^ k).val := by
    simp only [Units.val_pow_eq_pow_val]
  have h2 : (PowerSeries.invOneSubPow ℤ 1) ^ k = PowerSeries.invOneSubPow ℤ k := invOneSubPow_pow k
  rw [h1, h2]

/-- The coefficient of `x^n` in `(1-x)^{-k}` for `k > 0`. -/
theorem coeff_invOneSubPow (k n : ℕ) (hk : 0 < k) :
    (PowerSeries.invOneSubPow ℤ k).val.coeff n = Nat.choose (k - 1 + n) (k - 1) := by
  have := @PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ _ k hk
  rw [this]
  simp only [PowerSeries.coeff_mk]

/-- Coefficient of the geometric series `∑_{i<p} x^i` at `x^m`. -/
theorem coeff_geom_series (p m : ℕ) :
    (∑ i ∈ range p, (PowerSeries.X : PowerSeries ℤ) ^ i).coeff m = if m < p then 1 else 0 := by
  simp only [map_sum, PowerSeries.coeff_X_pow]
  rw [sum_ite_eq]
  simp [mem_range]

/-- Equivalence between `{x // x ∈ range k}` and `Fin k`. -/
private def rangeEquivFin (k : ℕ) : {x // x ∈ range k} ≃ Fin k where
  toFun x := ⟨x.val, mem_range.mp x.prop⟩
  invFun x := ⟨x.val, mem_range.mpr x.isLt⟩
  left_inv x := by simp
  right_inv x := by simp

/-- The sum over `range k` equals the sum over `Fin k`. -/
theorem sum_range_eq_sum_fin (k : ℕ) (l : ℕ →₀ ℕ) :
    ∑ i ∈ range k, l i = ∑ i : Fin k, l i.val := by
  rw [Fin.sum_univ_eq_sum_range (fun i => l i) k]

/-- The filtered finset of bounded antidiagonals. -/
def boundedAntidiag (n k p : ℕ) : Finset (ℕ →₀ ℕ) :=
  (finsuppAntidiag (range k) n).filter (fun l => ∀ i ∈ range k, l i < p)

/-- Forward direction of the bijection: bounded antidiagonal → BoundedWeakComposition. -/
noncomputable def antidiagToBwc (n k p : ℕ) : 
    boundedAntidiag n k p → BoundedWeakComposition n k p := fun l => by
  have hl := l.prop
  simp only [boundedAntidiag, mem_filter, mem_finsuppAntidiag] at hl
  exact ⟨fun i => ⟨l.val i.val, hl.2 i.val (mem_range.mpr i.isLt)⟩, by
    have h := sum_range_eq_sum_fin k l.val
    simp only [← hl.1.1, h]⟩

/-- Backward direction of the bijection: BoundedWeakComposition → bounded antidiagonal. -/
noncomputable def bwcToAntidiag (n k p : ℕ) : 
    BoundedWeakComposition n k p → boundedAntidiag n k p := fun α => by
  let f : ℕ → ℕ := fun i => if h : i < k then (α.val ⟨i, h⟩).val else 0
  have hf : ∀ a, f a ≠ 0 → a ∈ range k := by
    intro a ha
    by_cases h : a < k
    · exact mem_range.mpr h
    · simp only [f, h, dite_false, ne_eq, not_true_eq_false] at ha
  let l := Finsupp.onFinset (range k) f hf
  refine ⟨l, ?_⟩
  simp only [boundedAntidiag, mem_filter, mem_finsuppAntidiag]
  refine ⟨⟨?_, Finsupp.support_onFinset_subset⟩, ?_⟩
  · have hsum : ∑ i ∈ range k, l i = ∑ i : Fin k, (α.val i).val := by
      simp only [l, Finsupp.onFinset_apply]
      trans ∑ i ∈ range k, (if h : i < k then (α.val ⟨i, h⟩).val else 0)
      · rfl
      rw [sum_dite_of_true (fun i hi => mem_range.mp hi)]
      rw [← Equiv.sum_comp (rangeEquivFin k)]
      apply sum_congr rfl
      intro i _
      simp [rangeEquivFin]
    rw [hsum, α.prop]
  · intro i hi
    simp only [l, Finsupp.onFinset_apply, f, mem_range.mp hi, dite_true]
    exact (α.val ⟨i, mem_range.mp hi⟩).isLt

/-- Left inverse property of the bijection. -/
theorem bwc_left_inv (n k p : ℕ) (α : BoundedWeakComposition n k p) : 
    antidiagToBwc n k p (bwcToAntidiag n k p α) = α := by
  simp only [antidiagToBwc, bwcToAntidiag]
  congr 1
  ext i
  simp only [Finsupp.onFinset_apply, i.isLt, dite_true]

/-- Right inverse property of the bijection. -/
theorem bwc_right_inv (n k p : ℕ) (l : boundedAntidiag n k p) : 
    bwcToAntidiag n k p (antidiagToBwc n k p l) = l := by
  have hl := l.prop
  simp only [boundedAntidiag, mem_filter, mem_finsuppAntidiag] at hl
  simp only [antidiagToBwc, bwcToAntidiag]
  congr 1
  ext i
  simp only [Finsupp.onFinset_apply]
  by_cases hi : i < k
  · simp [hi]
  · have : l.val i = 0 := by
      by_contra h
      have h1 : i ∈ l.val.support := Finsupp.mem_support_iff.mpr h
      have h2 : i ∈ range k := hl.1.2 h1
      exact hi (mem_range.mp h2)
    simp [hi, this]

/-- The equivalence between bounded antidiagonals and BoundedWeakComposition. -/
noncomputable def bwcEquiv (n k p : ℕ) : 
    boundedAntidiag n k p ≃ BoundedWeakComposition n k p where
  toFun := antidiagToBwc n k p
  invFun := bwcToAntidiag n k p
  left_inv := bwc_right_inv n k p
  right_inv := bwc_left_inv n k p

/-- The cardinality of bounded antidiagonals equals the cardinality of BoundedWeakComposition. -/
theorem card_boundedAntidiag_eq (n k p : ℕ) :
    (boundedAntidiag n k p).card = Fintype.card (BoundedWeakComposition n k p) := by
  rw [← Fintype.card_coe]
  exact Fintype.card_eq.mpr ⟨bwcEquiv n k p⟩

/-- 
Key lemma: the coefficient of `x^n` in the generating function equals the count.

This is the standard fact that `[x^n](∑_{i<p} x^i)^k` counts k-tuples in `{0,...,p-1}^k` summing to `n`.
The proof uses the product rule for power series coefficients.
-/
theorem coeff_genFun (n k p : ℕ) :
    (genFun k p).coeff n = Fintype.card (BoundedWeakComposition n k p) := by
  unfold genFun
  rw [PowerSeries.coeff_pow]
  simp only [coeff_geom_series]
  -- The product is 1 iff all l i < p, else 0
  have h_prod : ∀ l : ℕ →₀ ℕ, (∏ i ∈ range k, (if l i < p then (1 : ℤ) else 0)) = 
      if ∀ i ∈ range k, l i < p then 1 else 0 := by
    intro l
    split_ifs with h
    · exact prod_eq_one (fun i hi => by simp [h i hi])
    · push Not at h
      obtain ⟨i, hi, hli⟩ := h
      exact prod_eq_zero hi (by simp [hli])
  simp_rw [h_prod]
  rw [sum_ite, sum_const_zero, add_zero, sum_const]
  simp only [nsmul_eq_mul, mul_one]
  -- Now: (filter (...) (finsuppAntidiag (range k) n)).card = Fintype.card (BoundedWeakComposition n k p)
  rw [show ({x ∈ (range k).finsuppAntidiag n | ∀ i ∈ range k, x i < p} : Finset (ℕ →₀ ℕ)) = 
       boundedAntidiag n k p from rfl]
  rw [card_boundedAntidiag_eq]

/-- 
The main coefficient extraction using the generating function approach.

Using `genFun k p = (1 - X^p)^k * (1-X)^{-k}` and the convolution formula:
- `(1-X^p)^k` has coefficient `(-1)^j C(k,j)` at `x^{pj}` for `j ≤ k`, else `0`
- `(1-X)^{-k}` has coefficient `C(k-1+m, k-1)` at `x^m` for `k > 0`

Convolving gives: `[x^n] = ∑_{pj ≤ n} (-1)^j C(k,j) * C(k-1+(n-pj), k-1)`
-/
-- The binomial expansion of (1 - X^p)^k
theorem one_sub_X_pow_pow_eq (p k : ℕ) : 
    (1 - (PowerSeries.X : PowerSeries ℤ) ^ p) ^ k = 
    ∑ j ∈ range (k + 1), PowerSeries.C ((-1 : ℤ) ^ j * (Nat.choose k j : ℤ)) * (PowerSeries.X : PowerSeries ℤ) ^ (p * j) := by
  conv_lhs => rw [sub_eq_add_neg, add_comm, add_pow]
  simp only [one_pow, mul_one]
  congr 1 with j
  have h1 : (-(PowerSeries.X : PowerSeries ℤ) ^ p) ^ j = (-1)^j * (PowerSeries.X ^ p)^j := by
    rw [neg_pow]
  rw [h1, pow_mul]
  congr 1
  calc ((-1 : PowerSeries ℤ) ^ j * (PowerSeries.X ^ p) ^ j * ↑(k.choose j) : PowerSeries ℤ)
      = (PowerSeries.X ^ p) ^ j * ((-1 : PowerSeries ℤ) ^ j * ↑(k.choose j)) := by ring
    _ = (PowerSeries.X ^ p) ^ j * PowerSeries.C ((-1 : ℤ) ^ j * ↑(k.choose j)) := by
        congr 1
        simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    _ = PowerSeries.C ((-1 : ℤ) ^ j * ↑(k.choose j)) * (PowerSeries.X ^ p) ^ j := by ring

-- Coefficient of X^n in (1 - X^p)^k
theorem coeff_one_sub_X_pow_pow (p k n : ℕ) :
    PowerSeries.coeff (R := ℤ) n ((1 - PowerSeries.X ^ p) ^ k) = 
      ∑ j ∈ (range (k + 1)).filter (fun j => p * j = n),
        (-1 : ℤ) ^ j * (Nat.choose k j : ℤ) := by
  rw [one_sub_X_pow_pow_eq]
  rw [map_sum]
  have h : ∀ j, (PowerSeries.coeff n) (PowerSeries.C ((-1 : ℤ) ^ j * (↑(k.choose j) : ℤ)) * (PowerSeries.X : PowerSeries ℤ) ^ (p * j)) = 
      if p * j = n then (-1 : ℤ)^j * (↑(k.choose j) : ℤ) else 0 := by
    intro j
    rw [PowerSeries.coeff_C_mul]
    simp only [PowerSeries.coeff_X_pow]
    split_ifs with h1 h2
    · ring
    · omega
    · omega
    · ring
  simp_rw [h]
  rw [sum_filter]

-- Helper lemma for binomial coefficient symmetry
theorem choose_symm_helper (n k : ℕ) (hk : 0 < k) : 
    (k - 1 + n).choose (k - 1) = (n + k - 1).choose n := by
  have h1 : k - 1 + n = n + (k - 1) := by omega
  have h2 : n + (k - 1) = n + k - 1 := by omega
  rw [h1, h2]
  have h3 : n + k - 1 = n + (k - 1) := by omega
  rw [h3]
  rw [Nat.choose_symm_add]

theorem coeff_genFun_formula (n k p : ℕ) :
    (genFun k p).coeff n = 
      ∑ j ∈ (range (k + 1)).filter (fun j => p * j ≤ n),
        (-1 : ℤ) ^ j * (Nat.choose k j) * (Nat.choose (n - p * j + k - 1) (n - p * j)) := by
  rw [genFun_eq, sum_filter]
  -- Handle the case k = 0 separately
  by_cases hk : k = 0
  · subst hk
    rw [pow_zero, one_mul, PowerSeries.invOneSubPow_zero, Units.val_one, PowerSeries.coeff_one]
    simp only [Nat.add_zero]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ite_false]
      have : n - 1 < n := Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.one_pos
      simp [Nat.choose_eq_zero_of_lt this]
  -- Now k > 0
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
  -- Use the convolution formula
  rw [PowerSeries.coeff_mul]
  -- Transform the antidiagonal sum
  rw [Nat.sum_antidiagonal_eq_sum_range_succ (f := fun m r => 
    (PowerSeries.coeff m) ((1 - PowerSeries.X ^ p) ^ k) * 
    (PowerSeries.coeff r) (PowerSeries.invOneSubPow ℤ k).val)]
  -- Expand the coefficient of (1-X^p)^k
  simp_rw [coeff_one_sub_X_pow_pow]
  -- Distribute the multiplication
  simp_rw [sum_mul]
  -- Swap the order of summation
  simp_rw [sum_filter]
  rw [sum_comm]
  -- Simplify using sum_ite_eq'
  conv_lhs =>
    arg 2
    ext j
    simp only [eq_comm (a := p * j)]
    rw [sum_ite_eq' (range (n + 1)) (p * j)]
    simp only [mem_range]
  -- Convert p * j < n + 1 to p * j ≤ n
  simp_rw [show ∀ j, p * j < n + 1 ↔ p * j ≤ n by intro j; omega]
  -- Apply sum_congr to match the terms
  apply sum_congr rfl
  intro j _
  split_ifs with h
  -- Case: p * j ≤ n
  rw [coeff_invOneSubPow k (n - p * j) hk_pos]
  have h_choose : (k - 1 + (n - p * j)).choose (k - 1) = (n - p * j + k - 1).choose (n - p * j) := by
    rw [choose_symm_helper (n - p * j) k hk_pos]
  rw [h_choose]; ring

/--
**Theorem thm.fps.comps.num-wpcomps-n-k**:
The number of `k`-tuples `(α₁, α₂, ..., αₖ) ∈ {0, 1, ..., p-1}^k`
satisfying `α₁ + α₂ + ... + αₖ = n` is
`∑_{j : p*j ≤ n} (-1)^j * C(k,j) * C(n - p*j + k - 1, n - p*j)`.

Note: The sum is restricted to `j` with `p * j ≤ n` because when `p * j > n`,
the mathematical binomial coefficient `C(n - p*j + k - 1, n - p*j)` should be 0
(as there are no compositions with negative sum), but `Nat.choose` with truncating
subtraction would give a non-zero value.

## Proof Strategy

The proof uses generating functions. The generating function for bounded weak compositions
is `W_{k,p} = (∑_{i=0}^{p-1} x^i)^k`, which equals `((1-x^p)/(1-x))^k = (1-x^p)^k * (1-x)^{-k}`.

Using binomial expansions:
- `(1-x^p)^k = ∑_{j=0}^k (-1)^j C(k,j) x^{pj}`
- `(1-x)^{-k} = ∑_{m≥0} C(m+k-1, m) x^m`

Convolving these gives the formula.
-/
theorem card (n k p : ℕ) :
    (Fintype.card (BoundedWeakComposition n k p) : ℤ) =
      ∑ j ∈ (range (k + 1)).filter (fun j => p * j ≤ n),
        (-1 : ℤ) ^ j * (Nat.choose k j) * (Nat.choose (n - p * j + k - 1) (n - p * j)) := by
  rw [← coeff_genFun]
  exact coeff_genFun_formula n k p

end BoundedWeakComposition
/-! ### Binary Strings Identity -/


/-- For f : Fin k → Fin 2, the sum of values equals the cardinality of the support (positions with value 1). -/
theorem sum_fin2_eq_card_support (k : ℕ) (f : Fin k → Fin 2) :
    ∑ i, (f i).val = (Finset.univ.filter (fun i => f i = 1)).card := by
  conv_lhs =>
    arg 2
    ext i
    rw [show (f i).val = if f i = 1 then 1 else 0 by
      rcases f i with ⟨v, hv⟩
      interval_cases v <;> simp]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]

/-- Elements of Fin 2 are either 0 or 1. -/
theorem fin2_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v <;> simp

/-- Bijection between binary k-strings with n ones and n-element subsets of Fin k. -/
def binaryStringEquiv (k n : ℕ) :
    BoundedWeakComposition n k 2 ≃ {s : Finset (Fin k) // s.card = n} where
  toFun := fun ⟨f, hf⟩ => ⟨Finset.univ.filter (fun i => f i = 1), by
    rw [← hf, sum_fin2_eq_card_support]⟩
  invFun := fun ⟨s, hs⟩ => ⟨fun i => if i ∈ s then 1 else 0, by
    rw [sum_fin2_eq_card_support]
    convert hs using 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      split_ifs at h with h' <;> simp_all
    · intro h
      simp only [h, ↓reduceIte]⟩
  left_inv := fun ⟨f, hf⟩ => by
    simp only
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases fin2_eq_zero_or_one (f i) with h | h <;> simp [h]
  right_inv := fun ⟨s, hs⟩ => by
    simp only
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h <;> simp [h]

end AlgebraicCombinatorics
