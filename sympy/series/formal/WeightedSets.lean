/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
/-!
# The Generating Function of a Weighted Set

This file formalizes the theory of weighted sets and their weight generating functions,
following Section sec.gf.weighted-set of the Algebraic Combinatorics notes.

A weighted set is a set equipped with a weight function to ℕ. When the set is "finite-type"
(only finitely many elements of each weight), we can define its weight generating function
as a formal power series.

## Main Definitions

* `WeightedSet`: A set with a weight function to ℕ
* `WeightedSet.IsFiniteType`: Predicate for finite-type weighted sets
* `WeightedSet.weightGenFun`: The weight generating function of a finite-type weighted set
* `WeightedSet.Isomorphism`: Weight-preserving bijections between weighted sets
* `WeightedSet.disjointUnion`: Disjoint union of weighted sets (A + B)
* `WeightedSet.prod`: Product of weighted sets (A × B) with additive weights
* `WeightedSet.pow`: Cartesian power of a weighted set
* `WeightedSet.tuples`: Infinite disjoint union W^0 + W^1 + W^2 + ... (Kleene star)

## Main Results

* `WeightedSet.weightGenFun_eq_of_isomorphic`: Isomorphic weighted sets have equal generating functions
* `WeightedSet.weightGenFun_disjointUnion`: ḡ(A + B) = ḡ(A) + ḡ(B)
* `WeightedSet.weightGenFun_prod`: ḡ(A × B) = ḡ(A) · ḡ(B)
* `WeightedSet.weightGenFun_pow`: ḡ(A^k) = ḡ(A)^k
* `DominoTilingsZ.tiling_decomposition_isomorphism`: D ≅ F^0 + F^1 + F^2 + ... (Lemma lem.gf.weighted-set.domino.fd)

## Applications

The file includes applications to:
* Counting compositions (recovering the formula for the generating function of compositions)
* Domino tilings of height-2 rectangles (connection to Fibonacci numbers)

Note: Height-3 domino tilings are handled in `Details/DominoTilings.lean`.

## References

* [Flajolet and Sedgewick, *Analytic Combinatorics*, Part A][FlaSed09]
* [Fink, *Enumerative Combinatorics*, §3.3-§3.4][Fink17]

## Tags

weighted set, generating function, combinatorial class, domino tiling
-/


open PowerSeries Finset BigOperators

noncomputable section

variable {R : Type*} [CommSemiring R]
/-! ### Weighted Sets -/


/-- A weighted set is a type equipped with a weight function to ℕ.
    (Definition \ref{def.gf-ws.weighted-sets}(a)) -/
structure WeightedSet (α : Type*) where
  /-- The weight function assigning a natural number to each element -/
  weight : α → ℕ

namespace WeightedSet

variable {α β γ : Type*}

/-- A weighted set is finite-type if for each n ∈ ℕ, there are only finitely many
    elements of weight n. (Definition \ref{def.gf-ws.weighted-sets}(b)) -/
def IsFiniteType (W : WeightedSet α) : Prop :=
  ∀ n : ℕ, Set.Finite {a : α | W.weight a = n}

/-- The set of elements of a given weight in a weighted set -/
def elementsOfWeight (W : WeightedSet α) (n : ℕ) : Set α :=
  {a : α | W.weight a = n}

/-- For a finite-type weighted set, the count of elements of weight n -/
def countOfWeight (W : WeightedSet α) (hft : W.IsFiniteType) (n : ℕ) : ℕ :=
  (hft n).toFinset.card
/-! ### Weight Generating Function -/


/-- The weight generating function of a finite-type weighted set is the FPS
    ∑_{n ∈ ℕ} (# of elements of weight n) · x^n.
    (Definition \ref{def.gf-ws.weighted-sets}(c)) -/
def weightGenFun (W : WeightedSet α) (hft : W.IsFiniteType) : R⟦X⟧ :=
  PowerSeries.mk fun n => (W.countOfWeight hft n : R)
/-! ### Isomorphisms of Weighted Sets -/


/-- An isomorphism between weighted sets is a weight-preserving bijection.
    (Definition \ref{def.gf-ws.weighted-sets}(d)) -/
structure Isomorphism (W₁ : WeightedSet α) (W₂ : WeightedSet β) where
  /-- The underlying bijection -/
  toEquiv : α ≃ β
  /-- The bijection preserves weights -/
  weight_eq : ∀ a : α, W₂.weight (toEquiv a) = W₁.weight a

/-- Two weighted sets are isomorphic if there exists an isomorphism between them.
    (Definition \ref{def.gf-ws.weighted-sets}(e)) -/
def AreIsomorphic (W₁ : WeightedSet α) (W₂ : WeightedSet β) : Prop :=
  Nonempty (Isomorphism W₁ W₂)

notation W₁ " ≅ᵥ " W₂ => AreIsomorphic W₁ W₂
/-! ### Disjoint Union of Weighted Sets -/


/-- The disjoint union of two weighted sets, with weights inherited from each component.
    (Definition \ref{def.gf-ws.djun}) -/
def disjointUnion (W₁ : WeightedSet α) (W₂ : WeightedSet β) : WeightedSet (α ⊕ β) where
  weight := Sum.elim W₁.weight W₂.weight

infixl:65 " +ᵥ " => disjointUnion
/-! ### Product of Weighted Sets -/


/-- The product of two weighted sets, with weight defined as the sum of component weights.
    (Definition \ref{def.gf-ws.prod}) -/
def prod (W₁ : WeightedSet α) (W₂ : WeightedSet β) : WeightedSet (α × β) where
  weight := fun ⟨a, b⟩ => W₁.weight a + W₂.weight b

infixl:70 " ×ᵥ " => prod
/-! ### Cartesian Powers -/


/-- The k-th Cartesian power of a weighted set.
    Weight of (a₁, ..., aₖ) is |a₁| + ... + |aₖ|. -/
def pow (W : WeightedSet α) (k : ℕ) : WeightedSet (Fin k → α) where
  weight := fun f => ∑ i, W.weight (f i)

/-- Helper: pow (n+1) is isomorphic to W × pow n -/
def pow_succ_equiv (W : WeightedSet α) (n : ℕ) :
    Isomorphism (W.pow (n + 1)) (W ×ᵥ (W.pow n)) where
  toEquiv := (Fin.succFunEquiv α n).trans (Equiv.prodComm _ _)
  weight_eq := fun f => by
    simp only [pow, prod, Equiv.trans_apply, Equiv.prodComm_apply, Fin.succFunEquiv]
    rw [Fin.sum_univ_castSucc, add_comm]
    simp [Fin.last, Fin.natAdd, Fin.castSucc, Fin.castAdd]
/-! ### Infinite Disjoint Union (Tuples) -/


/-- The infinite disjoint union W^0 + W^1 + W^2 + ... of all tuples of elements.
    This is the "Kleene star" construction on weighted sets.
    An element is a pair (k, f) where k ∈ ℕ and f : Fin k → α is a k-tuple.
    The weight of (k, f) is the sum of weights of the entries: ∑ᵢ |f(i)|. -/
def tuples (W : WeightedSet α) : WeightedSet (Σ n : ℕ, Fin n → α) where
  weight := fun ⟨n, f⟩ => ∑ i : Fin n, W.weight (f i)

/-- A weighted set has positive weights if every element has weight ≥ 1 -/
def HasPositiveWeights (W : WeightedSet α) : Prop :=
  ∀ a : α, W.weight a ≥ 1

end WeightedSet
/-! ### Examples and Applications -/


namespace WeightedSetExamples
/-! #### Binary Strings (Example \ref{exa.ws.bin-string1}) -/


/-- Binary strings (finite tuples of 0s and 1s) with weight = length -/
def BinaryStrings : WeightedSet (List (Fin 2)) where
  weight := List.length
/-! #### Positive Integers -/


/-- The positive integers with weight = value -/
def PositiveIntegers : WeightedSet ℕ+ where
  weight := fun n => n.val
/-! #### Compositions -/


/-- Compositions of length k are k-tuples of positive integers -/
def Compositions (k : ℕ) : WeightedSet (Fin k → ℕ+) :=
  PositiveIntegers.pow k

end WeightedSetExamples
/-! ### Domino Tilings -/


namespace DominoTilingsZ
/-! #### Shapes and Dominos (Definition \ref{def.domino.shapes-and-tilings}) -/


/-- A shape is a subset of ℤ² (Definition \ref{def.domino.shapes-and-tilings}(a)) -/
abbrev Shape := Set (ℤ × ℤ)

/-- The n × m rectangle (Definition \ref{def.domino.shapes-and-tilings}(b)) -/
def Rectangle (n m : ℕ) : Shape :=
  {p : ℤ × ℤ | 1 ≤ p.1 ∧ p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ m}

/-- The 0 × m rectangle is empty -/
@[simp]
theorem Rectangle_zero_left (m : ℕ) : Rectangle 0 m = ∅ := by
  ext p
  simp only [Rectangle, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  omega

/-- A domino is either horizontal or vertical (Definition \ref{def.domino.shapes-and-tilings}(c)) -/
inductive Domino : Type
  | horizontal (i j : ℤ) : Domino  -- {(i,j), (i+1,j)}
  | vertical (i j : ℤ) : Domino    -- {(i,j), (i,j+1)}
  deriving DecidableEq

/-- The cells covered by a domino -/
def Domino.toShape : Domino → Shape
  | .horizontal i j => {(i, j), (i + 1, j)}
  | .vertical i j => {(i, j), (i, j + 1)}

/-- The shape of a domino is nonempty -/
theorem Domino.toShape_nonempty (d : Domino) : d.toShape.Nonempty := by
  cases d with
  | horizontal i j => exact ⟨(i, j), Set.mem_insert _ _⟩
  | vertical i j => exact ⟨(i, j), Set.mem_insert _ _⟩

/-- A domino tiling of a shape S is a set partition of S into dominos
    (Definition \ref{def.domino.shapes-and-tilings}(d)) -/
structure Tiling (S : Shape) where
  /-- The set of dominos in the tiling -/
  dominos : Set Domino
  /-- The dominos are pairwise disjoint -/
  pairwise_disjoint : Set.PairwiseDisjoint dominos Domino.toShape
  /-- The union of dominos equals the shape -/
  cover : ⋃ d ∈ dominos, d.toShape = S

/-- Two tilings are equal iff they have the same dominos -/
@[ext]
theorem Tiling.ext {S : Shape} (T1 T2 : Tiling S) (h : T1.dominos = T2.dominos) : T1 = T2 := by
  cases T1
  cases T2
  congr

/-- The empty tiling of an empty shape -/
def Tiling.empty : Tiling ∅ where
  dominos := ∅
  pairwise_disjoint := Set.pairwiseDisjoint_empty
  cover := by simp

/-- The number of domino tilings of the n × m rectangle
    (Definition \ref{def.domino.shapes-and-tilings}(e))

    This is defined as the cardinality of the type of all tilings.
    Note: For this to be meaningful, the set of tilings must be finite,
    which holds for any finite rectangle. -/
def numTilings (n m : ℕ) : ℕ := Nat.card (Tiling (Rectangle n m))

notation "d_[" n "," m "]" => numTilings n m
/-! #### Height-2 Rectangle Tilings -/


/-- Domino tilings of height-2 rectangles, with weight = width of rectangle -/
def TilingsHeight2 : WeightedSet (Σ n : ℕ, Tiling (Rectangle n 2)) where
  weight := fun ⟨n, _⟩ => n

/-- A fault in a domino tiling is a vertical line that no domino straddles -/
def hasFault (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) : Prop :=
  k > 0 ∧ k < n ∧
  ∀ d ∈ T.dominos, match d with
    | .horizontal i _ => i < k ∨ i ≥ k + 1
    | .vertical _ _ => True

/-- hasFault only depends on the dominos set -/
theorem hasFault_eq_of_dominos_eq {n : ℕ} {T1 T2 : Tiling (Rectangle n 2)} 
    (h : T1.dominos = T2.dominos) (k : ℕ) : hasFault n T1 k ↔ hasFault n T2 k := by
  simp only [hasFault, h]

/-- A tiling is faultfree if it is nonempty and has no fault -/
def isFaultfree (n : ℕ) (T : Tiling (Rectangle n 2)) : Prop :=
  n > 0 ∧ ∀ k, ¬hasFault n T k

/-- Faultfree tilings of height-2 rectangles -/
def FaultfreeTilingsHeight2 : WeightedSet (Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T}) where
  weight := fun ⟨n, _⟩ => n
/-! ##### Helper lemmas for faultfree classification -/


theorem domino_subset_rect (n : ℕ) (T : Tiling (Rectangle n 2)) (d : Domino) (hd : d ∈ T.dominos) :
    d.toShape ⊆ Rectangle n 2 := by
  intro x hx
  have : x ∈ ⋃ d ∈ T.dominos, d.toShape := by
    simp only [Set.mem_iUnion]
    exact ⟨d, hd, hx⟩
  rw [T.cover] at this
  exact this

/-- The unique tiling of the 1×2 rectangle (one vertical domino) -/
def tiling_1_2 : Tiling (Rectangle 1 2) where
  dominos := {Domino.vertical 1 1}
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_singleton_iff] at hd1 hd2
    subst hd1 hd2
    exact (hne rfl).elim
  cover := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, exists_eq_left,
               Domino.toShape, Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact ⟨le_refl 1, le_refl 1, le_refl 1, by norm_num⟩
      · exact ⟨le_refl 1, le_refl 1, by norm_num, le_refl 2⟩
    · intro ⟨h1, h2, h3, h4⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      have hp1 : p.1 = 1 := by omega
      have hp2 : p.2 = 1 ∨ p.2 = 2 := by omega
      rcases hp2 with hp2eq | hp2eq
      · left; ext <;> omega
      · right; ext <;> omega

/-- The 1×2 tiling is faultfree -/
theorem tiling_1_2_faultfree : isFaultfree 1 tiling_1_2 := by
  constructor
  · omega
  · intro k ⟨hk1, hk2, _⟩
    omega

/-- The faultfree tiling of the 1×2 rectangle as a Subtype element -/
def faultfreeTiling_1_2 : {T : Tiling (Rectangle 1 2) // isFaultfree 1 T} :=
  ⟨tiling_1_2, tiling_1_2_faultfree⟩

/-- The unique faultfree tiling of width 2: two horizontal dominos -/
def twoHorizontalDominos : Tiling (Rectangle 2 2) where
  dominos := {Domino.horizontal 1 1, Domino.horizontal 1 2}
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd1 hd2
    rcases hd1 with rfl | rfl <;> rcases hd2 with rfl | rfl
    · exact (hne rfl).elim
    · simp only [Set.disjoint_iff, Set.subset_empty_iff]; ext x
      simp only [Domino.toShape, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
                 Set.mem_empty_iff_false, iff_false, not_and]
      intro h1; rcases h1 with rfl | rfl <;> (intro h2; rcases h2 with h | h <;> simp_all)
    · simp only [Set.disjoint_iff, Set.subset_empty_iff]; ext x
      simp only [Domino.toShape, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
                 Set.mem_empty_iff_false, iff_false, not_and]
      intro h1; rcases h1 with rfl | rfl <;> (intro h2; rcases h2 with h | h <;> simp_all)
    · exact (hne rfl).elim
  cover := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, exists_prop,
               Domino.toShape, Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro ⟨d, hd, hp⟩
      rcases hd with rfl | rfl <;>
        (simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp; rcases hp with rfl | rfl <;> omega)
    · intro ⟨h1, h2, h3, h4⟩
      have hp1 : p.1 = 1 ∨ p.1 = 2 := by omega
      have hp2 : p.2 = 1 ∨ p.2 = 2 := by omega
      rcases hp2 with hp2' | hp2'
      · use Domino.horizontal 1 1, Or.inl rfl
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hp1 with hp1' | hp1' <;> [left; right] <;> ext <;> omega
      · use Domino.horizontal 1 2, Or.inr rfl
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hp1 with hp1' | hp1' <;> [left; right] <;> ext <;> omega
/-! #### Decomposition Lemma (lem.gf.weighted-set.domino.fd) -/
/-! #### Helper definitions for tiling composition/decomposition -/


/-- Shift a domino horizontally by an offset -/
def Domino.shift (d : Domino) (offset : ℤ) : Domino :=
  match d with
  | .horizontal i j => .horizontal (i + offset) j
  | .vertical i j => .vertical (i + offset) j

/-- Shifting preserves the shape structure -/
theorem Domino.shift_toShape (d : Domino) (offset : ℤ) :
    (d.shift offset).toShape = d.toShape.image (fun p => (p.1 + offset, p.2)) := by
  cases d with
  | horizontal i j =>
    simp only [shift, toShape, Set.image_insert_eq, Set.image_singleton]
    ext ⟨x, y⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      · left; omega
      · right; omega
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      · left; omega
      · right; omega
  | vertical i j =>
    simp only [shift, toShape, Set.image_insert_eq, Set.image_singleton]

/-- Shift a set of dominos -/
def shiftDominos (ds : Set Domino) (offset : ℤ) : Set Domino :=
  ds.image (fun d => d.shift offset)

/-- Shifting by 0 is the identity -/
@[simp]
theorem Domino.shift_zero (d : Domino) : d.shift 0 = d := by
  cases d <;> simp [shift]

/-- Shifting twice is the same as shifting by the sum -/
theorem Domino.shift_shift (d : Domino) (a b : ℤ) : (d.shift a).shift b = d.shift (a + b) := by
  cases d <;> simp [shift, add_assoc]

/-- Rectangle shift lemma -/
theorem Rectangle_shift (n m : ℕ) (offset : ℤ) :
    (Rectangle n m).image (fun p => (p.1 + offset, p.2)) = 
    {p : ℤ × ℤ | 1 + offset ≤ p.1 ∧ p.1 ≤ n + offset ∧ 1 ≤ p.2 ∧ p.2 ≤ m} := by
  ext ⟨x, y⟩
  simp only [Set.mem_image, Rectangle, Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨x', y'⟩, ⟨h1, h2, h3, h4⟩, hx, hy⟩
    subst hx hy
    exact ⟨by omega, by omega, h3, h4⟩
  · intro ⟨h1, h2, h3, h4⟩
    refine ⟨(x - offset, y), ⟨by omega, by omega, h3, h4⟩, by omega, rfl⟩

/-- Shift a tiling to a new position -/
def Tiling.shift {n m : ℕ} (T : Tiling (Rectangle n m)) (offset : ℤ) :
    Tiling {p : ℤ × ℤ | 1 + offset ≤ p.1 ∧ p.1 ≤ n + offset ∧ 1 ≤ p.2 ∧ p.2 ≤ m} where
  dominos := shiftDominos T.dominos offset
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [shiftDominos, Set.mem_image] at hd1 hd2
    obtain ⟨d1', hd1', rfl⟩ := hd1
    obtain ⟨d2', hd2', rfl⟩ := hd2
    have hne' : d1' ≠ d2' := by
      intro heq; subst heq; exact hne rfl
    have hdisj := T.pairwise_disjoint hd1' hd2' hne'
    simp only [Function.onFun, Domino.shift_toShape]
    exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
      simp only [Prod.mk.injEq] at h
      ext <;> omega) hdisj
  cover := by
    have hcover := T.cover
    have heq : (Rectangle n m).image (fun p => (p.1 + offset, p.2)) = 
        {p : ℤ × ℤ | 1 + offset ≤ p.1 ∧ p.1 ≤ n + offset ∧ 1 ≤ p.2 ∧ p.2 ≤ m} := 
      Rectangle_shift n m offset
    rw [← heq]
    ext p
    simp only [Set.mem_iUnion, Set.mem_image, shiftDominos, exists_prop]
    constructor
    · rintro ⟨d, ⟨d', hd', rfl⟩, hp⟩
      rw [Domino.shift_toShape] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      have hp'_rect : p' ∈ Rectangle n m := by
        rw [← hcover]
        exact Set.mem_biUnion hd' hp'
      exact ⟨p', hp'_rect, rfl⟩
    · rintro ⟨p', hp', rfl⟩
      rw [← hcover] at hp'
      simp only [Set.mem_iUnion, exists_prop] at hp'
      obtain ⟨d', hd', hp''⟩ := hp'
      refine ⟨d'.shift offset, ⟨d', hd', rfl⟩, ?_⟩
      rw [Domino.shift_toShape]
      exact ⟨p', hp'', rfl⟩

/-- The tiling of the empty rectangle (width 0) -/
def emptyTiling2 : Tiling (Rectangle 0 2) := by
  rw [Rectangle_zero_left]
  exact Tiling.empty

/-- Cast a tiling along rectangle equality -/
def Tiling.cast {S S' : Shape} (h : S = S') (T : Tiling S) : Tiling S' where
  dominos := T.dominos
  pairwise_disjoint := T.pairwise_disjoint
  cover := by rw [← h]; exact T.cover

/-- Subst (▸) on a tiling preserves dominos -/
@[simp]
theorem Tiling.subst_dominos {n m : ℕ} (h : n = m) (T : Tiling (Rectangle n 2)) :
    (h ▸ T).dominos = T.dominos := by
  subst h
  rfl
/-! #### Composition: Concatenating faultfree tilings -/


/-- The partial sum of widths up to (but not including) index i -/
def partialWidthSum (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) : ℕ :=
  ∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1

/-- The partial width sum at index with val = 0 is always 0 -/
@[simp]
theorem partialWidthSum_zero (k : ℕ)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) (hi : i.val = 0) :
    partialWidthSum k ts i = 0 := by
  simp only [partialWidthSum]
  have hempty : (Finset.univ : Finset (Fin i.val)) = ∅ := by rw [hi]; rfl
  simp [hempty]

/-- Shift a domino by a natural number offset (for composition) -/
def Domino.shiftNat (d : Domino) (offset : ℕ) : Domino :=
  d.shift (offset : ℤ)

/-- Shifting by natural 0 is the identity -/
@[simp]
theorem Domino.shiftNat_zero (d : Domino) : d.shiftNat 0 = d := by
  simp [shiftNat, shift_zero]

/-- Shifting by natural number preserves shape structure -/
theorem Domino.shiftNat_toShape (d : Domino) (offset : ℕ) :
    (d.shiftNat offset).toShape = d.toShape.image (fun p => (p.1 + (offset : ℤ), p.2)) :=
  d.shift_toShape offset

/-- Shifting twice by natural numbers is the same as shifting by the sum -/
theorem Domino.shiftNat_shiftNat (d : Domino) (a b : ℕ) : 
    (d.shiftNat a).shiftNat b = d.shiftNat (a + b) := by
  simp only [shiftNat, shift_shift, Nat.cast_add]

/-- The set of dominos for the i-th component in the composition, shifted appropriately -/
def composeTilings_component_dominos (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) : Set Domino :=
  (ts i).2.val.dominos.image (fun d => d.shiftNat (partialWidthSum k ts i))

/-- The union of all shifted dominos for composition -/
def composeTilings_dominos (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) : Set Domino :=
  ⋃ i : Fin k, composeTilings_component_dominos k ts i

/-- X-coordinate bounds for a shifted domino from a component -/
theorem shifted_domino_x_in_range' {n : ℕ} {T : Tiling (Rectangle n 2)} {d : Domino}
    (hd : d ∈ T.dominos) (offset : ℕ) (p : ℤ × ℤ) (hp : p ∈ (d.shiftNat offset).toShape) :
    1 + (offset : ℤ) ≤ p.1 ∧ p.1 ≤ n + (offset : ℤ) := by
  rw [Domino.shiftNat_toShape] at hp
  obtain ⟨p', hp', rfl⟩ := hp
  have hsub := domino_subset_rect n T d hd hp'
  simp only [Rectangle, Set.mem_ofPred_eq] at hsub
  simp only
  constructor <;> linarith

/-- Helper lemma for finding which component a point belongs to based on its x-coordinate.
    Given k components with widths, finds the unique component containing position x. -/
theorem find_component_index (k : ℕ) (widths : Fin k → ℕ) (x : ℕ) (hx : x < ∑ i, widths i) :
    ∃ i : Fin k, (∑ j : Fin i.val, widths ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) ≤ x ∧ 
                 x < (∑ j : Fin i.val, widths ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) + widths i := by
  induction k with
  | zero => 
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hx
    omega
  | succ k ih =>
    by_cases h : x < ∑ i : Fin k, widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
    · have ih' := ih (fun i => widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) h
      obtain ⟨i, hi1, hi2⟩ := ih'
      exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hi1, hi2⟩
    · push Not at h
      have hsum : ∑ i : Fin (k + 1), widths i = 
          (∑ i : Fin k, widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + widths ⟨k, Nat.lt_succ_self k⟩ := by
        rw [Fin.sum_univ_castSucc]
        rfl
      have hx' : x < (∑ i : Fin k, widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + widths ⟨k, Nat.lt_succ_self k⟩ := by
        calc x < ∑ i : Fin (k + 1), widths i := hx
          _ = _ := hsum
      exact ⟨⟨k, Nat.lt_succ_self k⟩, h, hx'⟩

/-- Key lemma: partial width sums are monotonic -/
theorem partialWidthSum_add_le (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i1 i2 : Fin k) (h : i1 < i2) :
    partialWidthSum k ts i1 + (ts i1).1 ≤ partialWidthSum k ts i2 := by
  simp only [partialWidthSum]
  have hi : i1.val < i2.val := h
  have hle : i1.val + 1 ≤ i2.val := hi
  have hk : i1.val + 1 < k := Nat.lt_of_le_of_lt hi i2.isLt
  have hinj : Function.Injective (Fin.castLE hle) := Fin.castLE_injective hle
  have step1 : (∑ j : Fin i1.val, (ts ⟨j.val, Nat.lt_trans j.isLt i1.isLt⟩).1) + (ts i1).1 = 
               ∑ j : Fin (i1.val + 1), (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1 := by
    have heq := Fin.sum_univ_castSucc (fun j : Fin (i1.val + 1) => (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1)
    simp only [Fin.last, Fin.val_mk, Fin.val_castSucc] at heq
    linarith [heq]
  calc (∑ j : Fin i1.val, (ts ⟨j.val, Nat.lt_trans j.isLt i1.isLt⟩).1) + (ts i1).1
      = ∑ j : Fin (i1.val + 1), (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1 := step1
    _ = ∑ j : Fin (i1.val + 1), (ts ⟨(Fin.castLE hle j).val, Nat.lt_trans (Fin.castLE hle j).isLt i2.isLt⟩).1 := by
          apply Finset.sum_congr rfl; intro x _; simp [Fin.castLE]
    _ = ∑ j ∈ (Finset.univ : Finset (Fin (i1.val + 1))).map ⟨Fin.castLE hle, hinj⟩, 
          (ts ⟨j.val, Nat.lt_trans j.isLt i2.isLt⟩).1 := by
          rw [Finset.sum_map]; simp
    _ ≤ ∑ j : Fin i2.val, (ts ⟨j.val, Nat.lt_trans j.isLt i2.isLt⟩).1 := by
          apply Finset.sum_le_univ_sum_of_nonneg; intro _; exact Nat.zero_le _

/-- Helper: Dominos from different components have disjoint x-coordinate ranges -/
theorem composeTilings_component_dominos_disjoint (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i1 i2 : Fin k) (hi : i1 ≠ i2)
    (d1 : Domino) (hd1 : d1 ∈ composeTilings_component_dominos k ts i1)
    (d2 : Domino) (hd2 : d2 ∈ composeTilings_component_dominos k ts i2) :
    Disjoint d1.toShape d2.toShape := by
  -- Get the original dominos
  simp only [composeTilings_component_dominos, Set.mem_image] at hd1 hd2
  obtain ⟨d1', hd1', rfl⟩ := hd1
  obtain ⟨d2', hd2', rfl⟩ := hd2
  -- WLOG i1 < i2
  wlog h : i1 < i2 generalizing i1 i2 d1' d2' with H
  · have h' : i2 < i1 := (lt_or_gt_of_ne hi).resolve_left h
    exact (H i2 i1 (Ne.symm hi) d2' hd2' d1' hd1' h').symm
  -- Key: partialWidthSum i1 + (ts i1).1 ≤ partialWidthSum i2
  have key : partialWidthSum k ts i1 + (ts i1).1 ≤ partialWidthSum k ts i2 := 
    partialWidthSum_add_le k ts i1 i2 h
  -- Prove disjointness using x-coordinate separation
  rw [Set.disjoint_iff]
  intro p ⟨hp1, hp2⟩
  have hx1 := shifted_domino_x_in_range' hd1' (partialWidthSum k ts i1) p hp1
  have hx2 := shifted_domino_x_in_range' hd2' (partialWidthSum k ts i2) p hp2
  have h1 : p.1 ≤ (ts i1).1 + partialWidthSum k ts i1 := hx1.2
  have h2 : 1 + partialWidthSum k ts i2 ≤ p.1 := hx2.1
  have h3 : (ts i1).1 + partialWidthSum k ts i1 < 1 + partialWidthSum k ts i2 := by
    calc (ts i1).1 + partialWidthSum k ts i1 
        = partialWidthSum k ts i1 + (ts i1).1 := by ring
      _ ≤ partialWidthSum k ts i2 := key
      _ < 1 + partialWidthSum k ts i2 := by omega
  linarith

/-- For any point p in the rectangle of total width, there exists a component i such that
    partialWidthSum k ts i < p.1 ≤ partialWidthSum k ts i + (ts i).1 -/
theorem point_in_some_component (k : ℕ) (_hk : k ≥ 1)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (p : ℤ × ℤ) (hp : p ∈ Rectangle (∑ i : Fin k, (ts i).1) 2) :
    ∃ i : Fin k, (partialWidthSum k ts i : ℤ) < p.1 ∧ 
                  p.1 ≤ partialWidthSum k ts i + (ts i).1 := by
  simp only [Rectangle, Set.mem_ofPred_eq] at hp
  have hp1_pos : p.1 ≥ 1 := hp.1
  have hp1_le : p.1 ≤ ∑ i : Fin k, (ts i).1 := hp.2.1
  -- p.1 - 1 is in range [0, totalWidth - 1]
  have hp1_nat : (p.1 - 1).toNat < ∑ i : Fin k, (ts i).1 := by omega
  -- Find the component using find_component_index
  obtain ⟨i, hi_lo, hi_hi⟩ := find_component_index k (fun j => (ts j).1) (p.1 - 1).toNat hp1_nat
  refine ⟨i, ?_, ?_⟩
  · -- partialWidthSum k ts i < p.1
    simp only [partialWidthSum]
    have h : (∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1 : ℤ) ≤ (p.1 - 1).toNat := by
      exact_mod_cast hi_lo
    omega
  · -- p.1 ≤ partialWidthSum k ts i + (ts i).1
    simp only [partialWidthSum]
    have h : ((p.1 - 1).toNat : ℤ) < ∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1 + (ts i).1 := by
      exact_mod_cast hi_hi
    omega

/-- The composition function: given a tuple of faultfree tilings, concatenate them
    horizontally to produce a single tiling.
    
    Each faultfree tiling is shifted by the cumulative width of the previous tilings,
    and the union of all shifted dominos forms the composed tiling.
    
    This is the inverse of decomposeTiling. -/
def composeTilings (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    Σ n : ℕ, Tiling (Rectangle n 2) :=
  let totalWidth := ∑ i : Fin k, (ts i).1
  ⟨totalWidth, {
    dominos := composeTilings_dominos k ts
    pairwise_disjoint := by
      intro d1 hd1 d2 hd2 hne
      simp only [composeTilings_dominos, Set.mem_iUnion] at hd1 hd2
      obtain ⟨i1, hi1⟩ := hd1
      obtain ⟨i2, hi2⟩ := hd2
      simp only [composeTilings_component_dominos, Set.mem_image] at hi1 hi2
      obtain ⟨d1', hd1', rfl⟩ := hi1
      obtain ⟨d2', hd2', rfl⟩ := hi2
      -- The shifted dominos are disjoint either because they come from the same component
      -- (and the original dominos are disjoint) or from different components (different x-ranges)
      by_cases heq : i1 = i2
      · -- Same component: use original pairwise disjointness
        subst heq
        have hne' : d1' ≠ d2' := by
          intro h
          subst h
          exact hne rfl
        have hdisj := (ts i1).2.val.pairwise_disjoint hd1' hd2' hne'
        simp only [Function.onFun, Domino.shiftNat_toShape]
        exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
          simp only [Prod.mk.injEq] at h
          ext <;> omega) hdisj
      · -- Different components: disjoint x-ranges
        simp only [Function.onFun]
        exact composeTilings_component_dominos_disjoint k ts i1 i2 heq 
          (d1'.shiftNat (partialWidthSum k ts i1)) 
          (Set.mem_image_of_mem _ hd1')
          (d2'.shiftNat (partialWidthSum k ts i2)) 
          (Set.mem_image_of_mem _ hd2')
    cover := by
        -- The union of shifted dominos covers the rectangle of total width
        -- This follows from each component covering its portion of the rectangle
        ext ⟨x, y⟩
        simp only [Set.mem_iUnion, Rectangle, Set.mem_ofPred_eq]
        constructor
        · -- ⊆ direction: any point in a shifted domino is in the total rectangle
          rintro ⟨d, hd, hp⟩
          simp only [composeTilings_dominos, Set.mem_iUnion] at hd
          obtain ⟨i, hi⟩ := hd
          simp only [composeTilings_component_dominos, Set.mem_image] at hi
          obtain ⟨d', hd', rfl⟩ := hi
          -- Get x-coordinate bounds from shifted_domino_x_in_range'
          have hx := shifted_domino_x_in_range' hd' (partialWidthSum k ts i) (x, y) hp
          -- Get y-coordinate bounds from the original domino
          rw [Domino.shiftNat_toShape] at hp
          obtain ⟨⟨x', y'⟩, hp', heq⟩ := hp
          simp only [Prod.mk.injEq] at heq
          have hd'_rect := domino_subset_rect (ts i).1 (ts i).2.val d' hd' hp'
          simp only [Rectangle, Set.mem_ofPred_eq] at hd'_rect
          -- Bound for x: need partialWidthSum + (ts i).1 ≤ totalWidth
          have hbound : partialWidthSum k ts i + (ts i).1 ≤ ∑ j : Fin k, (ts j).1 := by
            simp only [partialWidthSum]
            have hsub : Finset.univ.map (Fin.castLEEmb i.isLt) ⊆ Finset.univ := 
              fun x _ => Finset.mem_univ x
            have h3 := Finset.sum_le_sum_of_subset (f := fun j => (ts j).1) hsub
            have h4 : ∑ j ∈ Finset.univ.map (Fin.castLEEmb i.isLt), (ts j).1 = 
                      ∑ j : Fin (i.val + 1), (ts ⟨j.val, Nat.lt_of_lt_of_le j.isLt i.isLt⟩).1 := by
              rw [Finset.sum_map]
              apply Finset.sum_congr rfl
              intro j _
              rfl
            have h5 : (∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1) + (ts i).1 = 
                      ∑ j : Fin (i.val + 1), (ts ⟨j.val, Nat.lt_of_lt_of_le j.isLt i.isLt⟩).1 := by
              rw [Fin.sum_univ_castSucc]
              simp only [Fin.val_castSucc, Fin.val_last]
            calc (∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1) + (ts i).1
                = ∑ j : Fin (i.val + 1), (ts ⟨j.val, Nat.lt_of_lt_of_le j.isLt i.isLt⟩).1 := h5
              _ = ∑ j ∈ Finset.univ.map (Fin.castLEEmb i.isLt), (ts j).1 := h4.symm
              _ ≤ ∑ j : Fin k, (ts j).1 := h3
          constructor
          · -- 1 ≤ x
            have : 1 + (partialWidthSum k ts i : ℤ) ≤ x := hx.1
            omega
          constructor
          · -- x ≤ totalWidth
            have : x ≤ (ts i).1 + (partialWidthSum k ts i : ℤ) := hx.2
            have : (partialWidthSum k ts i : ℤ) + (ts i).1 ≤ ∑ j : Fin k, (ts j).1 := by
              exact_mod_cast hbound
            omega
          constructor
          · -- 1 ≤ y
            have hy_eq : y = y' := heq.2.symm
            omega
          · -- y ≤ 2
            have hy_eq : y = y' := heq.2.symm
            omega
        · -- ⊇ direction: any point in the rectangle is covered by some shifted domino
          intro ⟨hx1, hx2, hy1, hy2⟩
          -- Handle k = 0 case: rectangle is empty
          by_cases hk : k = 0
          · -- k = 0 ⇒ totalWidth = 0, so 1 ≤ x ≤ 0 is impossible
            have htw : totalWidth = 0 := by
              simp only [totalWidth]
              subst hk
              rfl
            rw [htw] at hx2
            omega
          · -- k ≥ 1: use point_in_some_component
            have hk' : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
            have hp_rect : (x, y) ∈ Rectangle (∑ i : Fin k, (ts i).1) 2 := by
              simp only [Rectangle, Set.mem_ofPred_eq]
              exact ⟨hx1, hx2, hy1, hy2⟩
            obtain ⟨i, hi_lo, hi_hi⟩ := point_in_some_component k hk' ts (x, y) hp_rect
            -- The unshifted point (x - partialWidthSum, y) is in component i's rectangle
            have hp'_rect : (x - partialWidthSum k ts i, y) ∈ Rectangle (ts i).1 2 := by
              simp only [Rectangle, Set.mem_ofPred_eq]
              constructor
              · omega
              constructor
              · omega
              exact ⟨hy1, hy2⟩
            -- By component's cover property, this point is covered by some domino d'
            rw [← (ts i).2.val.cover] at hp'_rect
            simp only [Set.mem_iUnion] at hp'_rect
            obtain ⟨d', hd', hp'⟩ := hp'_rect
            -- The shifted domino d'.shiftNat (partialWidthSum k ts i) covers (x, y)
            refine ⟨d'.shiftNat (partialWidthSum k ts i), ?_, ?_⟩
            · -- Show the shifted domino is in composeTilings_dominos
              simp only [composeTilings_dominos, composeTilings_component_dominos, 
                         Set.mem_iUnion, Set.mem_image]
              exact ⟨i, d', hd', rfl⟩
            · rw [Domino.shiftNat_toShape]
              refine ⟨(x - partialWidthSum k ts i, y), hp', ?_⟩
              simp only [Prod.mk.injEq]
              constructor
              · omega
              · trivial
    }⟩

/-- For k = 1, the composed dominos equal the original dominos (shifted by 0) -/
theorem composeTilings_dominos_one 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    composeTilings_dominos 1 ts = (ts 0).2.val.dominos := by
  simp only [composeTilings_dominos, composeTilings_component_dominos]
  -- Union over Fin 1 is just the single element
  ext d
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨i, d', hd', rfl⟩
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    have h0 : (0 : Fin 1).val = 0 := rfl
    simp only [partialWidthSum_zero 1 ts 0 h0, Domino.shiftNat_zero]
    exact hd'
  · intro hd
    refine ⟨0, d, hd, ?_⟩
    have h0 : (0 : Fin 1).val = 0 := rfl
    simp only [partialWidthSum_zero 1 ts 0 h0, Domino.shiftNat_zero]

/-- For k = 1, the composed tiling has the same dominos as the original -/
theorem composeTilings_one_dominos 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings 1 ts).2.dominos = (ts 0).2.val.dominos := by
  simp only [composeTilings]
  exact composeTilings_dominos_one ts

/-- For k = 1, the width of the composed tiling equals the width of the single component -/
theorem composeTilings_one_width 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings 1 ts).1 = (ts 0).1 := by
  simp only [composeTilings, Finset.univ_unique, Finset.sum_singleton]
  rfl

/-- For k = 1, the composed tiling equals the single component (as Tilings) -/
theorem composeTilings_one_tiling 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings 1 ts).2 = (ts 0).2.val := by
  apply Tiling.ext
  exact composeTilings_one_dominos ts

/-- For k = 1, the composed tiling is faultfree -/
theorem composeTilings_one_isFaultfree 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    isFaultfree (composeTilings 1 ts).1 (composeTilings 1 ts).2 := by
  have h := (ts 0).2.property
  -- The width is (ts 0).1 and the tiling has the same dominos as (ts 0).2.val
  -- Since (ts 0).2.val is faultfree, so is the composed tiling
  constructor
  · -- Positive width
    have hpos : (ts 0).1 > 0 := h.1
    simp only [composeTilings, Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero]
    exact hpos
  · -- No faults
    intro k hfault
    have hno_fault := h.2 k
    apply hno_fault
    rw [hasFault_eq_of_dominos_eq (composeTilings_one_dominos ts).symm]
    simp only [composeTilings] at hfault ⊢
    exact hfault
/-! #### Decomposition: Cutting at faults -/
/-! ##### Infrastructure for restricting tilings at faults -/


/-- Shift a domino by a negative offset (for decomposition) -/
def Domino.shiftNeg (d : Domino) (offset : ℕ) : Domino :=
  d.shift (-(offset : ℤ))

/-- Shifting by negative offset preserves shape structure -/
theorem Domino.shiftNeg_toShape (d : Domino) (offset : ℕ) :
    (d.shiftNeg offset).toShape = d.toShape.image (fun p => (p.1 - (offset : ℤ), p.2)) := by
  simp only [shiftNeg, shift_toShape]
  ext ⟨x, y⟩
  simp only [Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨x', y'⟩, hp, hx, hy⟩
    exact ⟨⟨x', y'⟩, hp, by omega, hy⟩
  · rintro ⟨⟨x', y'⟩, hp, hx, hy⟩
    exact ⟨⟨x', y'⟩, hp, by omega, hy⟩

/-- Shifting by -k then by k returns the original domino -/
theorem Domino.shiftNat_shiftNeg (d : Domino) (k : ℕ) : (d.shiftNeg k).shiftNat k = d := by
  cases d <;> simp [shiftNat, shiftNeg, shift]

/-- A domino is in the left part (all x-coordinates ≤ k) -/
def Domino.inLeftPart (d : Domino) (k : ℕ) : Prop :=
  ∀ p ∈ d.toShape, p.1 ≤ k

/-- A domino is in the right part (all x-coordinates ≥ k+1) -/
def Domino.inRightPart (d : Domino) (k : ℕ) : Prop :=
  ∀ p ∈ d.toShape, p.1 ≥ k + 1

/-- At a fault, each domino is either entirely left or entirely right -/
theorem domino_left_or_right_at_fault {n : ℕ} {T : Tiling (Rectangle n 2)} {k : ℕ}
    (hk : hasFault n T k) (d : Domino) (hd : d ∈ T.dominos) :
    d.inLeftPart k ∨ d.inRightPart k := by
  cases d with
  | horizontal i j =>
    have hfault := hk.2.2 (Domino.horizontal i j) hd
    simp only [Domino.inLeftPart, Domino.inRightPart, Domino.toShape]
    rcases hfault with hlt | hge
    · left
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> simp <;> omega
    · right
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> simp <;> omega
  | vertical i j =>
    simp only [Domino.inLeftPart, Domino.inRightPart, Domino.toShape]
    -- Get x-coordinate bound from the domino being in the tiling
    have hsub := domino_subset_rect n T (Domino.vertical i j) hd
    have h1 : (i, j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
    simp only [Rectangle, Set.mem_ofPred_eq] at h1
    by_cases hi : i ≤ k
    · left
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> simp <;> omega
    · right
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> simp <;> omega

/-- Restrict a tiling to the left part at a fault position -/
def restrictTilingLeft (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk : hasFault n T k) : Tiling (Rectangle k 2) where
  dominos := {d ∈ T.dominos | d.inLeftPart k}
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_sep_iff] at hd1 hd2
    exact T.pairwise_disjoint hd1.1 hd2.1 hne
  cover := by
    ext ⟨x, y⟩
    simp only [Set.mem_iUnion, Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro ⟨d, ⟨hd, hleft⟩, hp⟩
      have hdomain := T.cover ▸ Set.mem_biUnion hd hp
      simp only [Rectangle, Set.mem_ofPred_eq] at hdomain
      exact ⟨hdomain.1, hleft (x, y) hp, hdomain.2.2.1, hdomain.2.2.2⟩
    · intro ⟨h1, h2, h3, h4⟩
      have hk_lt_n : (k : ℤ) < n := by exact_mod_cast hk.2.1
      have hxy : (x, y) ∈ Rectangle n 2 := by
        simp only [Rectangle, Set.mem_ofPred_eq]
        exact ⟨h1, by omega, h3, h4⟩
      rw [← T.cover] at hxy
      simp only [Set.mem_iUnion] at hxy
      obtain ⟨d, hd, hp⟩ := hxy
      have hlr := domino_left_or_right_at_fault hk d hd
      rcases hlr with hleft | hright
      · exact ⟨d, ⟨hd, hleft⟩, hp⟩
      · -- Contradiction: d is in right part but covers (x, y) with x ≤ k
        exfalso
        have hge := hright (x, y) hp
        omega

/-- Restrict a tiling to the right part at a fault position, shifted to origin -/
def restrictTilingRight (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk : hasFault n T k) : Tiling (Rectangle (n - k) 2) where
  dominos := ({d ∈ T.dominos | d.inRightPart k}).image (fun d => d.shiftNeg k)
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_image, Set.mem_sep_iff] at hd1 hd2
    obtain ⟨d1', ⟨hd1'_mem, _⟩, rfl⟩ := hd1
    obtain ⟨d2', ⟨hd2'_mem, _⟩, rfl⟩ := hd2
    have hne' : d1' ≠ d2' := by intro heq; subst heq; exact hne rfl
    have hdisj := T.pairwise_disjoint hd1'_mem hd2'_mem hne'
    simp only [Function.onFun, Domino.shiftNeg_toShape]
    exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
      simp only [Prod.mk.injEq] at h; ext <;> omega) hdisj
  cover := by
      ext ⟨x, y⟩
      simp only [Set.mem_iUnion, Set.mem_image, Rectangle, Set.mem_ofPred_eq]
      constructor
      · intro ⟨d, hd_img, hp⟩
        obtain ⟨d', ⟨hd', hright⟩, hd_eq⟩ := hd_img
        rw [← hd_eq, Domino.shiftNeg_toShape] at hp
        obtain ⟨p', hp', hp_eq⟩ := hp
        simp only [Prod.mk.injEq] at hp_eq
        have hdomain := T.cover ▸ Set.mem_biUnion hd' hp'
        simp only [Rectangle, Set.mem_ofPred_eq] at hdomain
        have hx : p'.1 ≥ k + 1 := hright p' hp'
        have hy : y = p'.2 := hp_eq.2.symm
        constructor
        · omega
        constructor
        · have hk_le_n : (k : ℤ) ≤ n := by exact_mod_cast Nat.le_of_lt hk.2.1
          omega
        constructor
        · rw [hy]; exact hdomain.2.2.1
        · rw [hy]; exact hdomain.2.2.2
      · intro ⟨h1, h2, h3, h4⟩
        have hk_lt_n : (k : ℤ) < n := by exact_mod_cast hk.2.1
        have hxy : ((x + k : ℤ), y) ∈ Rectangle n 2 := by
          simp only [Rectangle, Set.mem_ofPred_eq]
          exact ⟨by omega, by omega, h3, h4⟩
        rw [← T.cover] at hxy
        simp only [Set.mem_iUnion] at hxy
        obtain ⟨d, hd, hp⟩ := hxy
        have hlr := domino_left_or_right_at_fault hk d hd
        rcases hlr with hleft | hright
        · -- Contradiction: d is in left part but covers (x + k, y) with x ≥ 1
          exfalso
          have hle := hleft ((x + k : ℤ), y) hp
          omega
        · refine ⟨d.shiftNeg k, ⟨d, ⟨hd, hright⟩, rfl⟩, ?_⟩
          rw [Domino.shiftNeg_toShape]
          refine ⟨((x + k : ℤ), y), hp, ?_⟩
          simp only [add_sub_cancel_right]

/-- The left restriction at a fault is faultfree if k is the smallest fault -/
theorem restrictTilingLeft_isFaultfree (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk : hasFault n T k) (hmin : ∀ j, j < k → ¬hasFault n T j) : 
    isFaultfree k (restrictTilingLeft n T k hk) := by
  constructor
  · exact hk.1
  · intro j hfault_restr
    -- We need to show False (i.e., no fault at j in the restricted tiling)
    -- A fault at j in the restricted tiling would imply a fault at j in T
    -- But j < k and hmin says there's no fault at j in T
    have hj_lt : j < k := hfault_restr.2.1
    have hj_lt_n : j < n := Nat.lt_trans hj_lt hk.2.1
    have hfault_T : hasFault n T j := by
      refine ⟨hfault_restr.1, hj_lt_n, ?_⟩
      intro d hd
      cases d with
      | horizontal i jj =>
        -- If d is in T.dominos, it's either in left part or right part
        have hlr := domino_left_or_right_at_fault hk (Domino.horizontal i jj) hd
        rcases hlr with hleft | hright
        · -- d is in left part, so it's in the restricted tiling
          have hd_restr : Domino.horizontal i jj ∈ (restrictTilingLeft n T k hk).dominos := by
            simp only [restrictTilingLeft, Set.mem_sep_iff]
            exact ⟨hd, hleft⟩
          exact hfault_restr.2.2 (Domino.horizontal i jj) hd_restr
        · -- d is in right part (x ≥ k+1), so i ≥ k+1 > j, hence i ≥ j+1
          simp only [Domino.inRightPart, Domino.toShape] at hright
          have hi := hright (i, jj) (by simp)
          have hj_lt_k : (j : ℤ) < k := by exact_mod_cast hj_lt
          right
          -- Need to show i ≥ j + 1
          -- We have hi : i ≥ k + 1 and hj_lt : j < k
          -- So i ≥ k + 1 > k > j, hence i ≥ j + 1
          omega
      | vertical _ _ => trivial
    exact hmin j hj_lt hfault_T

/-- The original dominos equal the union of left part and shifted right part -/
theorem dominos_eq_left_union_shifted_right (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk : hasFault n T k) : 
    T.dominos = (restrictTilingLeft n T k hk).dominos ∪ 
                ((restrictTilingRight n T k hk).dominos.image (fun d => d.shiftNat k)) := by
  ext d
  simp only [Set.mem_union, Set.mem_image]
  simp only [restrictTilingLeft, restrictTilingRight, Set.mem_sep_iff, Set.mem_image]
  constructor
  · intro hd
    rcases domino_left_or_right_at_fault hk d hd with hleft | hright
    · left; exact ⟨hd, hleft⟩
    · right
      -- d is in right part, so d.shiftNeg k is in restrictTilingRight
      -- and (d.shiftNeg k).shiftNat k = d
      refine ⟨d.shiftNeg k, ⟨d, ⟨hd, hright⟩, rfl⟩, ?_⟩
      exact d.shiftNat_shiftNeg k
  · intro hd
    rcases hd with ⟨hd, _⟩ | ⟨d', ⟨d'', ⟨hd'', _⟩, hd'_eq⟩, hd_eq⟩
    · exact hd
    · -- d = d'.shiftNat k where d' = d''.shiftNeg k and d'' ∈ T.dominos
      subst hd'_eq hd_eq
      rw [Domino.shiftNat_shiftNeg]
      exact hd''

/-- The set of fault positions in a tiling -/
def faultPositions (n : ℕ) (T : Tiling (Rectangle n 2)) : Set ℕ :=
  {k | hasFault n T k}

/-- The fault positions form a finite set (bounded by n) -/
theorem faultPositions_finite (n : ℕ) (T : Tiling (Rectangle n 2)) : 
    (faultPositions n T).Finite := by
  apply Set.Finite.subset (Set.finite_Icc 0 n)
  intro k hk
  simp only [faultPositions, Set.mem_ofPred_eq] at hk
  simp only [Set.mem_Icc]
  exact ⟨Nat.zero_le k, Nat.le_of_lt hk.2.1⟩

/-- The minimum fault position in a tiling (when faults exist) -/
noncomputable def minFault (n : ℕ) (T : Tiling (Rectangle n 2)) 
    (hne : (faultPositions n T).Nonempty) : ℕ :=
  (faultPositions_finite n T).toFinset.min' (by
    rw [Set.Finite.toFinset_nonempty]
    exact hne)

/-- The minimum fault is indeed a fault -/
theorem minFault_mem (n : ℕ) (T : Tiling (Rectangle n 2)) 
    (hne : (faultPositions n T).Nonempty) : minFault n T hne ∈ faultPositions n T := by
  unfold minFault
  have := (faultPositions_finite n T).toFinset.min'_mem (by
    rw [Set.Finite.toFinset_nonempty]; exact hne)
  simp only [Set.Finite.mem_toFinset] at this
  exact this

/-- The minimum fault is a hasFault -/
theorem minFault_hasFault (n : ℕ) (T : Tiling (Rectangle n 2)) 
    (hne : (faultPositions n T).Nonempty) : hasFault n T (minFault n T hne) :=
  minFault_mem n T hne

/-- The minimum fault is less than or equal to any other fault -/
theorem minFault_le (n : ℕ) (T : Tiling (Rectangle n 2)) 
    (hne : (faultPositions n T).Nonempty) (j : ℕ) (hj : j ∈ faultPositions n T) :
    minFault n T hne ≤ j := by
  unfold minFault
  apply (faultPositions_finite n T).toFinset.min'_le
  simp only [Set.Finite.mem_toFinset]
  exact hj

/-- Decidability instance for faultPositions.Nonempty -/
noncomputable instance faultPositions_nonempty_decidable (n : ℕ) (T : Tiling (Rectangle n 2)) : 
    Decidable (faultPositions n T).Nonempty := by
  have h := (faultPositions_finite n T).toFinset.decidableNonempty
  rw [Set.Finite.toFinset_nonempty] at h
  exact h

/-- A faultfree tiling has no faults, so faultPositions is empty -/
theorem faultPositions_empty_of_isFaultfree (n : ℕ) (T : Tiling (Rectangle n 2)) 
    (hff : isFaultfree n T) : faultPositions n T = ∅ := by
  ext k
  simp only [faultPositions, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact hff.2 k

/-- A faultfree tiling has non-nonempty faultPositions -/
theorem faultPositions_not_nonempty_of_isFaultfree (n : ℕ) (T : Tiling (Rectangle n 2)) 
    (hff : isFaultfree n T) : ¬(faultPositions n T).Nonempty := by
  rw [faultPositions_empty_of_isFaultfree n T hff]
  exact Set.not_nonempty_empty
/-! ##### Helper lemmas for k >= 2 case of decomposeTiling_composeTilings -/

/-- For k >= 2, the composed tiling has a fault at position (ts 0).1 -/
theorem composeTilings_hasFault_at_boundary (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1 := by
  -- Need to show: (ts 0).1 > 0, (ts 0).1 < total width, and no horizontal domino crosses position (ts 0).1
  set w0 := (ts ⟨0, by omega⟩).1 with hw0_def
  have hpos : w0 > 0 := (ts ⟨0, by omega⟩).2.property.1
  -- Total width is sum of all component widths
  have htotal : (composeTilings k ts).1 = ∑ i : Fin k, (ts i).1 := rfl
  -- Since k >= 2, there's at least one more component with positive width
  have hlt : w0 < (composeTilings k ts).1 := by
    rw [htotal]
    have h1 : (ts ⟨1, by omega⟩).1 > 0 := (ts ⟨1, by omega⟩).2.property.1
    have hdiff : (⟨0, by omega⟩ : Fin k) ≠ (⟨1, by omega⟩ : Fin k) := by simp
    have hsum : w0 + (ts ⟨1, by omega⟩).1 ≤ ∑ i : Fin k, (ts i).1 := by
      have := Finset.sum_pair hdiff (f := fun i => (ts i).1)
      calc w0 + (ts ⟨1, by omega⟩).1 
          = ∑ i ∈ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin k)), (ts i).1 := by rw [this]
        _ ≤ ∑ i : Fin k, (ts i).1 := by
          apply Finset.sum_le_sum_of_subset
          intro i _
          exact Finset.mem_univ i
    omega
  constructor
  · exact hpos
  constructor
  · exact hlt
  · -- Show no horizontal domino crosses position w0
    intro d hd
    simp only [composeTilings, composeTilings_dominos, Set.mem_iUnion] at hd
    obtain ⟨j, hj⟩ := hd
    simp only [composeTilings_component_dominos, Set.mem_image] at hj
    obtain ⟨d', hd', rfl⟩ := hj
    -- d' is a domino from component j, shifted by partialWidthSum k ts j
    cases d' with
    | horizontal i jj =>
      -- Horizontal domino at position i in component j
      -- After shifting, position is i + partialWidthSum k ts j
      simp only [Domino.shiftNat, Domino.shift]
      -- Case split on j
      by_cases hj0 : j.val = 0
      · -- j = 0: domino from first component
        left
        have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
        have hpws : partialWidthSum k ts j = 0 := by
          rw [hj_eq]
          exact partialWidthSum_zero k ts ⟨0, by omega⟩ rfl
        simp only [hpws, Nat.cast_zero, add_zero]
        -- d' = horizontal i jj is in (ts j).2.val.dominos
        -- Since ts j is faultfree with width (ts j).1, we have i < (ts j).1
        have hd'_in : Domino.horizontal i jj ∈ (ts j).2.val.dominos := hd'
        have hsub := domino_subset_rect (ts j).1 (ts j).2.val (Domino.horizontal i jj) hd'_in
        -- The domino's rightmost point (i+1, jj) is in Rectangle (ts j).1 2
        have hright : (i + 1, jj) ∈ (Domino.horizontal i jj).toShape := by simp [Domino.toShape]
        have hright_rect := hsub hright
        simp only [Rectangle, Set.mem_ofPred_eq] at hright_rect
        -- hright_rect : 1 ≤ i + 1 ∧ i + 1 ≤ (ts j).1 ∧ 1 ≤ jj ∧ jj ≤ 2
        -- We need i < w0, i.e., i < (ts ⟨0, _⟩).1
        -- Since j = ⟨0, _⟩, we have (ts j).1 = w0
        have hw0_eq : (ts j).1 = w0 := by rw [hj_eq]
        have hi_bound : i + 1 ≤ w0 := by rw [← hw0_eq]; exact hright_rect.2.1
        linarith
      · -- j >= 1: domino from later component
        right
        have hj_pos : j.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hj0
        have hj1 : (⟨0, by omega⟩ : Fin k) < j := by simp [Fin.lt_def]; omega
        have hpws_ge : partialWidthSum k ts j ≥ w0 := by
          have := partialWidthSum_add_le k ts ⟨0, by omega⟩ j hj1
          simp only [hw0_def] at this ⊢
          omega
        -- The shifted position is i + partialWidthSum k ts j >= 1 + w0 = w0 + 1
        have hi_pos : i ≥ 1 := by
          have hd'_in : Domino.horizontal i jj ∈ (ts j).2.val.dominos := hd'
          have hsub := domino_subset_rect (ts j).1 (ts j).2.val (Domino.horizontal i jj) hd'_in
          have hleft : (i, jj) ∈ (Domino.horizontal i jj).toShape := by simp [Domino.toShape]
          have hleft_rect := hsub hleft
          simp only [Rectangle, Set.mem_ofPred_eq] at hleft_rect
          omega
        calc (i : ℤ) + (partialWidthSum k ts j : ℤ) 
            ≥ 1 + (w0 : ℤ) := by omega
          _ = (w0 : ℤ) + 1 := by ring
    | vertical i jj =>
      -- Vertical dominos don't affect faults
      trivial

/-- For k >= 1, there are no faults at positions less than (ts 0).1 in the composed tiling -/
theorem composeTilings_no_fault_before_boundary (k : ℕ) (hk : k ≥ 1)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (p : ℕ) (hp : p < (ts ⟨0, hk⟩).1) : ¬hasFault (composeTilings k ts).1 (composeTilings k ts).2 p := by
  intro hfault
  -- If there's a fault at p < (ts 0).1, then the first component would have a fault at p
  -- But the first component is faultfree, contradiction
  have hff := (ts ⟨0, hk⟩).2.property
  have hno_fault := hff.2 p
  apply hno_fault
  -- Show hasFault (ts 0).1 (ts 0).2.val p
  have hpos : p > 0 := hfault.1
  have hlt : p < (ts ⟨0, hk⟩).1 := hp
  constructor
  · exact hpos
  constructor
  · exact hlt
  · -- Show no horizontal domino in (ts 0).2.val crosses position p
    intro d hd
    -- d is in (ts 0).2.val.dominos
    -- The shifted version d.shiftNat 0 = d is in composeTilings_dominos
    have hd_shifted : d.shiftNat (partialWidthSum k ts ⟨0, hk⟩) ∈ (composeTilings k ts).2.dominos := by
      simp only [composeTilings, composeTilings_dominos, Set.mem_iUnion]
      refine ⟨⟨0, hk⟩, ?_⟩
      simp only [composeTilings_component_dominos, Set.mem_image]
      exact ⟨d, hd, rfl⟩
    have hpws0 : partialWidthSum k ts ⟨0, hk⟩ = 0 := partialWidthSum_zero k ts ⟨0, hk⟩ rfl
    simp only [hpws0, Domino.shiftNat_zero] at hd_shifted
    -- Use the fault condition at p in the composed tiling
    have hcross := hfault.2.2 d hd_shifted
    exact hcross

/-- The minimum fault in a composed tiling with k >= 2 components is at (ts 0).1 -/
theorem composeTilings_minFault_eq (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) 
    (hne : (faultPositions (composeTilings k ts).1 (composeTilings k ts).2).Nonempty) :
    minFault (composeTilings k ts).1 (composeTilings k ts).2 hne = (ts ⟨0, by omega⟩).1 := by
  -- The minimum fault is (ts 0).1 because:
  -- 1. There's a fault at (ts 0).1 (by composeTilings_hasFault_at_boundary)
  -- 2. There are no faults at positions < (ts 0).1 (by composeTilings_no_fault_before_boundary)
  have hfault := composeTilings_hasFault_at_boundary k hk ts
  have hmin := minFault_hasFault (composeTilings k ts).1 (composeTilings k ts).2 hne
  have hle := minFault_le (composeTilings k ts).1 (composeTilings k ts).2 hne (ts ⟨0, by omega⟩).1 hfault
  -- Show minFault >= (ts 0).1 by contradiction
  by_contra hne'
  push Not at hne'
  have hlt : minFault (composeTilings k ts).1 (composeTilings k ts).2 hne < (ts ⟨0, by omega⟩).1 := by
    omega
  have hno := composeTilings_no_fault_before_boundary k (by omega : k ≥ 1) ts 
    (minFault (composeTilings k ts).1 (composeTilings k ts).2 hne) hlt
  exact hno hmin
/-! ##### Lemmas relating restrictTiling to composeTilings -/


/-- The tail of a tuple of faultfree tilings -/
def faultfreeTilingsTail (k : ℕ) (hk : k ≥ 1)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    Fin (k - 1) → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}) :=
  fun i => ts ⟨i.val + 1, by omega⟩

/-- The width of composing the tail equals the total width minus the first component width -/
theorem composeTilings_tail_width (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).1 = 
    (composeTilings k ts).1 - (ts ⟨0, by omega⟩).1 := by
  simp only [composeTilings, faultfreeTilingsTail]
  -- Sum over tail = total sum - first element
  have hsplit : ∑ i : Fin k, (ts i).1 = (ts ⟨0, by omega⟩).1 + 
                ∑ i : Fin (k - 1), (ts ⟨i.val + 1, by omega⟩).1 := by
    induction k with
    | zero => omega
    | succ n ih =>
      cases n with
      | zero => omega
      | succ m =>
        rw [Fin.sum_univ_succ]
        rfl
  omega

/-- Dominos from component 0 are in the left part at position (ts 0).1 -/
theorem composeTilings_component0_inLeftPart (k : ℕ) (hk : k ≥ 1)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (d : Domino) (hd : d ∈ (ts ⟨0, hk⟩).2.val.dominos) :
    d.inLeftPart (ts ⟨0, hk⟩).1 := by
  intro p hp
  have hsub := domino_subset_rect (ts ⟨0, hk⟩).1 (ts ⟨0, hk⟩).2.val d hd
  have hp_rect := hsub hp
  simp only [Rectangle, Set.mem_ofPred_eq] at hp_rect
  exact hp_rect.2.1

/-- Dominos from component i >= 1 are in the right part at position (ts 0).1 -/
theorem composeTilings_componentPos_inRightPart (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) (hi : i.val ≥ 1) (d : Domino) (hd : d ∈ (ts i).2.val.dominos) :
    (d.shiftNat (partialWidthSum k ts i)).inRightPart (ts ⟨0, by omega⟩).1 := by
  intro p hp
  -- The shifted domino has x-coordinates >= partialWidthSum k ts i + 1
  -- Since i >= 1, partialWidthSum k ts i >= (ts 0).1
  have hpws_ge : partialWidthSum k ts i ≥ (ts ⟨0, by omega⟩).1 := by
    have h0 : (⟨0, by omega⟩ : Fin k) < i := by simp [Fin.lt_def]; omega
    have := partialWidthSum_add_le k ts ⟨0, by omega⟩ i h0
    omega
  -- The original domino d has x-coords in [1, (ts i).1]
  have hd_x := domino_subset_rect (ts i).1 (ts i).2.val d hd
  -- After shifting, x-coords are in [1 + pws, (ts i).1 + pws]
  rw [Domino.shiftNat_toShape, Set.mem_image] at hp
  obtain ⟨p', hp', hp_eq⟩ := hp
  rw [Prod.ext_iff] at hp_eq
  have hp'_rect := hd_x hp'
  simp only [Rectangle, Set.mem_ofPred_eq] at hp'_rect
  have hx' : p'.1 ≥ 1 := hp'_rect.1
  calc p.1 = p'.1 + partialWidthSum k ts i := by omega
    _ ≥ 1 + (ts ⟨0, by omega⟩).1 := by omega
    _ = (ts ⟨0, by omega⟩).1 + 1 := by ring

/-- The left restriction of a composed tiling at the first boundary has the same dominos 
    as the first component -/
theorem restrictTilingLeft_composeTilings_dominos (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) 
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    (restrictTilingLeft (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault).dominos = (ts ⟨0, by omega⟩).2.val.dominos := by
  ext d
  simp only [restrictTilingLeft, composeTilings, composeTilings_dominos,
             Set.mem_iUnion, composeTilings_component_dominos, Set.mem_image]
  constructor
  · -- If d is in the left restriction, it came from component 0
    intro ⟨⟨i, d', hd', hd_eq⟩, hleft⟩
    -- d = d'.shiftNat (partialWidthSum k ts i)
    subst hd_eq
    -- If i = 0, then partialWidthSum = 0 and d' is in (ts 0).2.val.dominos
    -- If i >= 1, then d is in right part, contradiction with hleft
    by_cases hi : i.val = 0
    · -- i = 0
      have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi
      rw [hi_eq] at hd' ⊢
      have hpws : partialWidthSum k ts ⟨0, by omega⟩ = 0 := 
        partialWidthSum_zero k ts ⟨0, by omega⟩ rfl
      rw [hpws, Domino.shiftNat_zero]
      exact hd'
    · -- i >= 1, contradiction
      exfalso
      have hi_pos : i.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
      have hright := composeTilings_componentPos_inRightPart k hk ts i hi_pos d' hd'
      -- d'.shiftNat ... is in right part, but hleft says it's in left part
      have hcontra := hleft
      simp only [Domino.inLeftPart] at hcontra
      simp only [Domino.inRightPart] at hright
      -- Get a point in d'.shiftNat ...
      have hne := Domino.toShape_nonempty (d'.shiftNat (partialWidthSum k ts i))
      obtain ⟨p, hp⟩ := hne
      have h1 := hcontra p hp
      have h2 := hright p hp
      omega
  · -- If d is in (ts 0).2.val.dominos, it's in the composed tiling and in left part
    intro hd
    constructor
    · -- d is in composeTilings_dominos
      refine ⟨⟨0, by omega⟩, d, hd, ?_⟩
      have hpws : partialWidthSum k ts ⟨0, by omega⟩ = 0 := 
        partialWidthSum_zero k ts ⟨0, by omega⟩ rfl
      rw [hpws, Domino.shiftNat_zero]
    · -- d is in left part
      exact composeTilings_component0_inLeftPart k (by omega) ts d hd

/-- The left restriction of a composed tiling equals the first component's tiling.
    This follows from `restrictTilingLeft_composeTilings_dominos` via `Tiling.ext`. -/
theorem restrictTilingLeft_composeTilings_eq (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    restrictTilingLeft (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault = (ts ⟨0, by omega⟩).2.val := by
  apply Tiling.ext
  exact restrictTilingLeft_composeTilings_dominos k hk ts hfault

/-- Dominos from component i shifted and then unshifted by k gives back the original -/
theorem composeTilings_componentPos_dominos_unshift (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) (hi : i.val ≥ 1) (d : Domino) (hd : d ∈ (ts i).2.val.dominos) :
    (d.shiftNat (partialWidthSum k ts i)).shiftNeg (ts ⟨0, by omega⟩).1 = 
    d.shiftNat (partialWidthSum k ts i - (ts ⟨0, by omega⟩).1) := by
  -- partialWidthSum k ts i >= (ts 0).1 for i >= 1
  have hpws_ge : partialWidthSum k ts i ≥ (ts ⟨0, by omega⟩).1 := by
    have h0 : (⟨0, by omega⟩ : Fin k) < i := by simp [Fin.lt_def]; omega
    have := partialWidthSum_add_le k ts ⟨0, by omega⟩ i h0
    omega
  cases d with
  | horizontal x y =>
    simp only [Domino.shiftNat, Domino.shiftNeg, Domino.shift]
    congr 1
    omega
  | vertical x y =>
    simp only [Domino.shiftNat, Domino.shiftNeg, Domino.shift]
    congr 1
    omega

/-- The partial width sum for the tail equals the original minus (ts 0).1 -/
theorem partialWidthSum_tail (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (j : Fin (k - 1)) :
    partialWidthSum (k - 1) (faultfreeTilingsTail k (by omega) ts) j = 
    partialWidthSum k ts ⟨j.val + 1, by omega⟩ - (ts ⟨0, by omega⟩).1 := by
  simp only [partialWidthSum, faultfreeTilingsTail]
  -- LHS: ∑ i : Fin j.val, (ts ⟨i.val + 1, ...⟩).1
  -- RHS: ∑ i : Fin (j.val + 1), (ts ⟨i.val, ...⟩).1 - (ts ⟨0, ...⟩).1
  -- Use Fin.sum_univ_succ on RHS
  have hrhs : ∑ i : Fin (j.val + 1), (ts ⟨i.val, by omega⟩).1 = 
              (ts ⟨0, by omega⟩).1 + ∑ i : Fin j.val, (ts ⟨i.succ.val, by omega⟩).1 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero]
  conv_rhs => rw [hrhs]
  -- Now goal: ∑ i : Fin j.val, (ts ⟨i.val + 1, ...⟩).1 = 
  --           (ts ⟨0, ...⟩).1 + ∑ i : Fin j.val, (ts ⟨i.succ.val, ...⟩).1 - (ts ⟨0, ...⟩).1
  -- Note: i.succ.val = i.val + 1
  have heq : ∑ i : Fin j.val, (ts ⟨i.succ.val, by omega⟩).1 = 
             ∑ i : Fin j.val, (ts ⟨i.val + 1, by omega⟩).1 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.val_succ]
  rw [heq]
  omega

/-- The right restriction of a composed tiling at the first boundary has the same dominos 
    as the composition of the tail -/
theorem restrictTilingRight_composeTilings_dominos (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) 
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    (restrictTilingRight (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault).dominos = 
    (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).2.dominos := by
  -- The proof shows that:
  -- 1. Dominos in right restriction come from components i >= 1
  -- 2. After unshifting by (ts 0).1, they match the tail composition
  ext d
  simp only [restrictTilingRight, Set.mem_image, composeTilings, 
             composeTilings_dominos, Set.mem_iUnion, composeTilings_component_dominos]
  constructor
  · -- Forward direction: d is in restrictTilingRight → d is in composeTilings of tail
    intro ⟨d', ⟨⟨i, d'', hd'', hd'_eq⟩, hright⟩, hd_eq⟩
    -- d' = d''.shiftNat (partialWidthSum k ts i) is in right part
    -- d = d'.shiftNeg w0 = (d''.shiftNat (pws k ts i)).shiftNeg w0
    subst hd'_eq hd_eq
    -- If i = 0, then d' would be in left part (contradiction)
    -- So i >= 1
    by_cases hi : i.val = 0
    · -- i = 0: contradiction
      exfalso
      have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi
      rw [hi_eq] at hd'' hright
      have hpws : partialWidthSum k ts ⟨0, by omega⟩ = 0 := partialWidthSum_zero k ts ⟨0, by omega⟩ rfl
      rw [hpws, Domino.shiftNat_zero] at hright
      have hleft := composeTilings_component0_inLeftPart k (by omega : k ≥ 1) ts d'' hd''
      -- d'' is in left part but hright says it's in right part
      have hne := Domino.toShape_nonempty d''
      obtain ⟨p, hp⟩ := hne
      have h1 := hleft p hp
      have h2 := hright p hp
      omega
    · -- i >= 1: d comes from component i
      have hi_pos : i.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
      -- The index in the tail is i - 1
      -- Need to show d'' is in (faultfreeTilingsTail k _ ts ⟨i.val - 1, _⟩).2.val.dominos
      have hd''_tail : d'' ∈ (faultfreeTilingsTail k (by omega) ts ⟨i.val - 1, by omega⟩).2.val.dominos := by
        simp only [faultfreeTilingsTail]
        have hi_eq' : i.val - 1 + 1 = i.val := by omega
        have hfin_eq : (⟨i.val - 1 + 1, by omega⟩ : Fin k) = i := Fin.ext hi_eq'
        rw [hfin_eq]
        exact hd''
      refine ⟨⟨i.val - 1, by omega⟩, d'', hd''_tail, ?_⟩
      -- Need: (d''.shiftNat (pws k ts i)).shiftNeg w0 = d''.shiftNat (pws (k-1) (tail) (i-1))
      -- Use composeTilings_componentPos_dominos_unshift and partialWidthSum_tail
      have hunshift := composeTilings_componentPos_dominos_unshift k hk ts i hi_pos d'' hd''
      rw [hunshift]
      congr 1
      have htail := partialWidthSum_tail k hk ts ⟨i.val - 1, by omega⟩
      -- htail says: pws (k-1) (tail ts) ⟨i.val - 1, _⟩ = pws k ts ⟨i.val - 1 + 1, _⟩ - w0
      -- We need: pws k ts i - w0 = pws (k-1) (tail ts) ⟨i.val - 1, _⟩
      have hi_eq' : i.val - 1 + 1 = i.val := by omega
      have hfin_eq : (⟨i.val - 1 + 1, by omega⟩ : Fin k) = i := Fin.ext hi_eq'
      rw [htail, hfin_eq]
  · -- Backward direction: d is in composeTilings of tail → d is in restrictTilingRight
    intro ⟨j, d', hd', hd_eq⟩
    -- j : Fin (k - 1), d' is in (tail ts j).2.val.dominos
    -- d = d'.shiftNat (pws (k-1) (tail ts) j)
    subst hd_eq
    -- The original index is j + 1
    let i : Fin k := ⟨j.val + 1, by omega⟩
    -- d' is in (ts i).2.val.dominos (since tail ts j = ts (j+1))
    have hd'_ts : d' ∈ (ts i).2.val.dominos := by
      simp only [faultfreeTilingsTail] at hd'
      exact hd'
    -- The shifted domino in composeTilings is d'.shiftNat (pws k ts i)
    have hi_pos : i.val ≥ 1 := by simp only [i, Nat.add_one_le_iff, Nat.zero_lt_succ]
    -- Show that d'.shiftNat (pws k ts i) is in right part
    have hright := composeTilings_componentPos_inRightPart k hk ts i hi_pos d' hd'_ts
    -- The unshifted version
    have hunshift := composeTilings_componentPos_dominos_unshift k hk ts i hi_pos d' hd'_ts
    -- pws (k-1) (tail ts) j = pws k ts i - w0
    have htail := partialWidthSum_tail k hk ts j
    -- So d'.shiftNat (pws (k-1) (tail ts) j) = (d'.shiftNat (pws k ts i)).shiftNeg w0
    refine ⟨d'.shiftNat (partialWidthSum k ts i), ⟨⟨i, d', hd'_ts, rfl⟩, hright⟩, ?_⟩
    rw [hunshift, htail]

/-- The right restriction of a composed tiling has the same dominos as the composition of the tail.
    Note: The tilings have different types (different width parameters), so we state this 
    as a domino equality rather than a tiling equality. Use `Tiling.ext` with the width 
    equality `composeTilings_tail_width` to convert to tiling equality when needed. -/
theorem restrictTilingRight_composeTilings_dominos_eq (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    (restrictTilingRight (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault).dominos = 
    (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).2.dominos :=
  restrictTilingRight_composeTilings_dominos k hk ts hfault

/-- The right restriction of a composed tiling equals the composition of the tail.
    This combines the width equality `composeTilings_tail_width` with the domino equality
    `restrictTilingRight_composeTilings_dominos_eq` to give a full tiling equality.
    
    Note: The two tilings have the same type because:
    - restrictTilingRight has width (composeTilings k ts).1 - (ts 0).1
    - composeTilings (k-1) (tail ts) has width (composeTilings k ts).1 - (ts 0).1 (by composeTilings_tail_width) -/
theorem restrictTilingRight_composeTilings_eq (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    restrictTilingRight (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault = 
    (composeTilings_tail_width k hk ts) ▸ (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).2 := by
  -- The dominos are equal by restrictTilingRight_composeTilings_dominos_eq
  have hdominos := restrictTilingRight_composeTilings_dominos_eq k hk ts hfault
  -- Apply Tiling.ext after casting
  apply Tiling.ext
  rw [hdominos]
  -- The cast doesn't change dominos
  rw [Tiling.subst_dominos]

/-- The decomposition function: given a tiling of a height-2 rectangle, produce a tuple
    of faultfree tilings by cutting along all faults.
    
    For example, a tiling with faults at positions k₁ < k₂ < ... < kₘ decomposes into
    m+1 faultfree tilings of widths k₁, k₂-k₁, ..., n-kₘ.
    
    The empty tiling (n=0) decomposes into the empty tuple (k=0). 
    
    Implementation: We recursively find the minimum fault position, cut the tiling there,
    and decompose the right part. The left part at a minimum fault is always faultfree.
    If no faults exist, the entire tiling is faultfree and returned as a singleton. -/
noncomputable def decomposeTiling : (n : ℕ) → (T : Tiling (Rectangle n 2)) → 
    Σ k : ℕ, Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})
  | 0, _ => ⟨0, Fin.elim0⟩
  | n + 1, T => 
    if hne : (faultPositions (n + 1) T).Nonempty then
      -- Has faults: cut at minimum fault
      let k := minFault (n + 1) T hne
      have hk : hasFault (n + 1) T k := minFault_hasFault (n + 1) T hne
      have hk_min : ∀ j, j < k → ¬hasFault (n + 1) T j := by
        intro j hj hfault
        have hle := minFault_le (n + 1) T hne j hfault
        omega
      let left := restrictTilingLeft (n + 1) T k hk
      let left_ff := restrictTilingLeft_isFaultfree (n + 1) T k hk hk_min
      let right := restrictTilingRight (n + 1) T k hk
      have hk_pos : k > 0 := hk.1
      have hk_lt : k < n + 1 := hk.2.1
      have hdec : n + 1 - k < n + 1 := by omega
      let ⟨m, ts⟩ := decomposeTiling (n + 1 - k) right
      ⟨m + 1, fun i => 
        if hi : i.val = 0 then ⟨k, ⟨left, left_ff⟩⟩ 
        else ts ⟨i.val - 1, by omega⟩⟩
    else
      -- No faults: T is faultfree
      have hff : isFaultfree (n + 1) T := by
        constructor
        · omega
        · intro k hfault
          exact hne ⟨k, hfault⟩
      ⟨1, fun _ => ⟨n + 1, ⟨T, hff⟩⟩⟩
termination_by n => n

/-- Decomposing a tiling with faults at the minimum fault position.
    This characterizes the structure of decomposeTiling when faults exist. -/
theorem decomposeTiling_hasFault (n : ℕ) (T : Tiling (Rectangle (n + 1) 2))
    (hne : (faultPositions (n + 1) T).Nonempty) :
    let k := minFault (n + 1) T hne
    let hk := minFault_hasFault (n + 1) T hne
    let hk_min : ∀ j, j < k → ¬hasFault (n + 1) T j := fun j hj hfault => 
      absurd (minFault_le (n + 1) T hne j hfault) (not_le.mpr hj)
    let left := restrictTilingLeft (n + 1) T k hk
    let left_ff := restrictTilingLeft_isFaultfree (n + 1) T k hk hk_min
    let right := restrictTilingRight (n + 1) T k hk
    let ⟨m, ts⟩ := decomposeTiling (n + 1 - k) right
    decomposeTiling (n + 1) T = 
      ⟨m + 1, fun i => if hi : i.val = 0 then ⟨k, ⟨left, left_ff⟩⟩ 
                       else ts ⟨i.val - 1, by omega⟩⟩ := by
  simp only [decomposeTiling, dite_eq_left hne]

/-- Decomposition followed by composition gives back the original tiling -/
theorem composeTilings_decomposeTiling (n : ℕ) (T : Tiling (Rectangle n 2)) :
    let ⟨k, ts⟩ := decomposeTiling n T
    composeTilings k ts = ⟨n, T⟩ := by
  simp only
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      -- n = 0 case: decomposeTiling returns ⟨0, Fin.elim0⟩
      have hdec : decomposeTiling 0 T = ⟨0, Fin.elim0⟩ := by unfold decomposeTiling; rfl
      rw [hdec]
      have hdom : (composeTilings 0 Fin.elim0).2.dominos = T.dominos := by
        cases T with
        | mk dominos pairwise_disjoint cover =>
          have hT_empty : dominos = ∅ := by
            have heqR : Rectangle 0 2 = ∅ := Rectangle_zero_left 2
            have hcover' : ⋃ d ∈ dominos, d.toShape = ∅ := by rw [cover]; exact heqR
            by_contra hne
            have hne' : dominos.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
            obtain ⟨d, hd⟩ := hne'
            have hsub : d.toShape ⊆ ∅ := by
              calc d.toShape ⊆ ⋃ d' ∈ dominos, d'.toShape := Set.subset_biUnion_of_mem hd
                _ = ∅ := hcover'
            have hdne : d.toShape.Nonempty := Domino.toShape_nonempty d
            exact Set.not_nonempty_empty (hdne.mono hsub)
          simp only [composeTilings, hT_empty]
          ext x
          simp only [composeTilings_dominos, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
          intro ⟨i, _⟩
          exact i.elim0
      have hw : (composeTilings 0 Fin.elim0).1 = 0 := by
        simp only [composeTilings, Finset.univ_eq_empty, Finset.sum_empty]
      apply Sigma.ext hw
      exact (eqRec_heq (φ := fun n => Tiling (Rectangle n 2)) hw (composeTilings 0 Fin.elim0).2).symm.trans
        (heq_of_eq <| by
          apply Tiling.ext
          simpa [Tiling.subst_dominos hw] using hdom)
    | n' + 1 =>
      -- n = n' + 1 case
      -- decomposeTiling (n' + 1) T branches on whether faults exist
      -- Case split on whether faults exist
      by_cases hne : (faultPositions (n' + 1) T).Nonempty
      · -- Has faults: cut at minimum fault
        -- Get the minimum fault position and related data
        set k := minFault (n' + 1) T hne with hk_def
        have hk : hasFault (n' + 1) T k := minFault_hasFault (n' + 1) T hne
        have hk_min : ∀ j, j < k → ¬hasFault (n' + 1) T j := by
          intro j hj hfault
          have hle := minFault_le (n' + 1) T hne j hfault
          omega
        have hk_pos : k > 0 := hk.1
        have hk_lt : k < n' + 1 := hk.2.1
        have hdec : n' + 1 - k < n' + 1 := by omega
        
        -- Set up the left and right parts
        set left := restrictTilingLeft (n' + 1) T k hk with hleft_def
        set right := restrictTilingRight (n' + 1) T k hk with hright_def
        have left_ff := restrictTilingLeft_isFaultfree (n' + 1) T k hk hk_min
        
        -- Get the decomposition of the right part (keeping definitional equality)
        set dec_right := decomposeTiling (n' + 1 - k) right with hdec_right_def
        
        -- Apply induction hypothesis to the right part
        have ih_right := ih (n' + 1 - k) hdec right
        -- ih_right : composeTilings dec_right.1 dec_right.2 = ⟨n' + 1 - k, right⟩
        
        -- Rewrite using decomposeTiling_hasFault to get the concrete form
        have hdecomp := decomposeTiling_hasFault n' T hne
        simp only at hdecomp
        rw [hdecomp]
        
        -- The goal is now in terms of the concrete decomposition
        -- We need to show that composing gives back ⟨n' + 1, T⟩
        
        -- Key facts we'll use:
        -- 1. ih_right tells us composeTilings on the right part gives back right
        -- 2. dominos_eq_left_union_shifted_right tells us T.dominos = left ∪ shifted(right)
        
        -- The proof strategy is to show both components are equal
        -- For this, we use the fact that Sigma types are equal iff both components are equal
        
        -- Define abbreviations for clarity
        let m := (decomposeTiling (n' + 1 - k) right).1
        let ts_rest := (decomposeTiling (n' + 1 - k) right).2
        
        -- Show the width equality first
        have hwidth : (composeTilings (m + 1) (fun i => 
            if hi : i.val = 0 then ⟨k, ⟨left, left_ff⟩⟩ else ts_rest ⟨i.val - 1, by omega⟩)).1 = n' + 1 := by
          simp only [composeTilings]
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, Fin.val_succ, ↓reduceDIte, Nat.add_sub_cancel]
          have hsum : ∑ x : Fin m,
              (if h : x.val + 1 = 0 then ⟨k, ⟨left, left_ff⟩⟩ else ts_rest ⟨x.val, by omega⟩).1
              = ∑ i : Fin m, (ts_rest i).1 := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [dite_eq_right (Nat.add_one_ne_zero x.val)]
          rw [hsum]
          have h := congrArg Sigma.fst ih_right
          simp only [composeTilings] at h
          rw [h]
          omega
        
        -- For the tiling part, we need to show the dominos are equal
        -- This requires showing that the union of shifted components equals T.dominos
        -- 
        -- The proof involves showing:
        -- 1. Component 0 (left) contributes left.dominos (shifted by 0)
        -- 2. Components 1..m contribute the shifted composition of ts_rest
        -- 3. By IH, composeTilings m ts_rest = right
        -- 4. By dominos_eq_left_union_shifted_right, T.dominos = left ∪ shifted(right)
        
        -- Define the function ts' for clarity
        let ts' : Fin (m + 1) → (Σ w : ℕ, {T' : Tiling (Rectangle w 2) // isFaultfree w T'}) := 
          fun i => if hi : i.val = 0 then ⟨k, ⟨left, left_ff⟩⟩ else ts_rest ⟨i.val - 1, by omega⟩
        
        -- Show the dominos equality
        -- composeTilings_dominos (m + 1) ts' = T.dominos
        -- By dominos_eq_left_union_shifted_right:
        -- T.dominos = left.dominos ∪ right.dominos.image (shiftNat k)
        
        have hT_dominos := dominos_eq_left_union_shifted_right (n' + 1) T k hk
        
        -- Show that the composed dominos equal left ∪ shifted(right)
        have hdominos_eq : (composeTilings (m + 1) ts').2.dominos = T.dominos := by
          -- Step 1: composeTilings dominos = composeTilings_dominos
          simp only [composeTilings]
          
          -- Step 2: Split the union into component 0 and components 1..m
          have hsplit : composeTilings_dominos (m + 1) ts' = 
              composeTilings_component_dominos (m + 1) ts' 0 ∪ 
              ⋃ j : Fin m, composeTilings_component_dominos (m + 1) ts' j.succ := by
            ext d
            simp only [composeTilings_dominos, Set.mem_iUnion, Set.mem_union]
            constructor
            · intro ⟨i, hi⟩
              rcases i.eq_zero_or_eq_succ with rfl | ⟨j, rfl⟩
              · left; exact hi
              · right; exact ⟨j, hi⟩
            · intro h
              rcases h with h | ⟨j, hj⟩
              · exact ⟨0, h⟩
              · exact ⟨j.succ, hj⟩
          rw [hsplit]
          
          -- Step 3: Component 0 is left.dominos (since partialWidthSum = 0)
          have hcomp0 : composeTilings_component_dominos (m + 1) ts' 0 = left.dominos := by
            simp only [composeTilings_component_dominos]
            have hpws0 : partialWidthSum (m + 1) ts' 0 = 0 := 
              partialWidthSum_zero (m + 1) ts' 0 rfl
            rw [hpws0]
            simp only [Domino.shiftNat_zero, Set.image_id']
            -- ts' 0 = ⟨k, ⟨left, left_ff⟩⟩
            have hts'0 : ts' 0 = ⟨k, ⟨left, left_ff⟩⟩ := by
              simp only [ts', Fin.val_zero, ↓reduceDIte]
            rw [hts'0]
          rw [hcomp0]
          
          -- Step 4: Show components 1..m equal right.dominos.image (shiftNat k)
          -- First, show the relationship between ts' j.succ and ts_rest j
          have hts'_succ : ∀ j : Fin m, ts' j.succ = ts_rest j := by
            intro j
            simp only [ts']
            simp only [Fin.val_succ, Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]
            rfl
          
          -- Key: partialWidthSum (m+1) ts' j.succ = k + partialWidthSum m ts_rest j
          have hpws_succ : ∀ j : Fin m, 
              partialWidthSum (m + 1) ts' j.succ = k + partialWidthSum m ts_rest j := by
            intro j
            simp only [partialWidthSum]
            -- The sum over Fin j.succ.val needs to be rewritten
            -- j.succ.val = j.val + 1
            -- We need: ∑ i : Fin (j.val + 1), (ts' ⟨i, ...⟩).1 = k + ∑ i : Fin j.val, (ts_rest ⟨i, ...⟩).1
            
            -- Define a simpler function for the sum
            let f : Fin j.succ.val → ℕ := fun i => (ts' ⟨i.val, Nat.lt_trans i.isLt j.succ.isLt⟩).1
            let g : Fin j.val → ℕ := fun i => (ts_rest ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩).1
            
            -- j.succ.val = j.val + 1 ≥ 1, so Fin j.succ.val has a 0 element
            have hpos : j.succ.val > 0 := by simp only [Fin.val_succ]; omega
            let zero_idx : Fin j.succ.val := ⟨0, hpos⟩
            
            -- Show f zero_idx = k
            have hf0 : f zero_idx = k := by
              simp only [f, zero_idx, ts', ↓reduceDIte]
            
            -- Show f i.succ = g i for i : Fin j.val
            have hf_succ : ∀ i : Fin j.val, f i.succ = g i := by
              intro i
              simp only [f, g, ts']
              simp only [Fin.val_succ, Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]
            
            -- Now use Fin.sum_univ_succ on f
            have h_sum : ∑ i : Fin j.succ.val, f i = f zero_idx + ∑ i : Fin j.val, f i.succ := by
              have h := Fin.sum_univ_succ f
              convert h using 2
              exact congrArg f (Fin.ext rfl).symm
            
            calc ∑ i : Fin j.succ.val, (ts' ⟨i.val, Nat.lt_trans i.isLt j.succ.isLt⟩).1
                = ∑ i : Fin j.succ.val, f i := rfl
              _ = f zero_idx + ∑ i : Fin j.val, f i.succ := h_sum
              _ = k + ∑ i : Fin j.val, f i.succ := by rw [hf0]
              _ = k + ∑ i : Fin j.val, g i := by simp only [hf_succ]
              _ = k + ∑ i : Fin j.val, (ts_rest ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩).1 := rfl
          
          -- Now show ⋃ j : Fin m, composeTilings_component_dominos (m+1) ts' j.succ
          --         = (composeTilings_dominos m ts_rest).image (shiftNat k)
          have hrest : ⋃ j : Fin m, composeTilings_component_dominos (m + 1) ts' j.succ = 
              (composeTilings_dominos m ts_rest).image (fun d => d.shiftNat k) := by
            ext d
            simp only [Set.mem_iUnion, composeTilings_component_dominos, Set.mem_image,
                       composeTilings_dominos]
            constructor
            · -- Forward: d is in component j.succ of ts'
              intro ⟨j, hj⟩
              obtain ⟨d', hd', hd_eq⟩ := hj
              use d'.shiftNat (partialWidthSum m ts_rest j)
              constructor
              · -- d'.shiftNat (partialWidthSum m ts_rest j) is in composeTilings_dominos m ts_rest
                refine ⟨j, d', ?_, rfl⟩
                rw [hts'_succ] at hd'
                exact hd'
              · -- d = (d'.shiftNat ...).shiftNat k
                rw [← hd_eq, hpws_succ, Nat.add_comm, Domino.shiftNat_shiftNat]
            · -- Backward: d is in (composeTilings_dominos m ts_rest).image (shiftNat k)
              intro ⟨d'', hd''_mem, hd_eq⟩
              obtain ⟨j, d', hd', hd''_eq⟩ := hd''_mem
              refine ⟨j, ?_⟩
              refine ⟨d', ?_, ?_⟩
              · rw [hts'_succ]; exact hd'
              · rw [← hd_eq, ← hd''_eq, hpws_succ, Nat.add_comm, Domino.shiftNat_shiftNat]
          rw [hrest]
          
          -- Step 5: Use IH to relate composeTilings_dominos m ts_rest to right.dominos
          have hih_dominos : (composeTilings m ts_rest).2.dominos = right.dominos := by
            have h := congrArg (fun σ => σ.2.dominos) ih_right
            exact h
          
          -- composeTilings_dominos m ts_rest = (composeTilings m ts_rest).2.dominos
          have hcomp_dominos : composeTilings_dominos m ts_rest = (composeTilings m ts_rest).2.dominos := by
            simp only [composeTilings]
          
          rw [hcomp_dominos, hih_dominos]
          
          -- Step 6: Apply dominos_eq_left_union_shifted_right
          exact hT_dominos.symm
        
        -- Now use the dominos equality to prove the full equality
        -- We need: composeTilings (m + 1) ts' = ⟨n' + 1, T⟩
        -- We have: hwidth for the first component
        -- We have: hdominos_eq for the second component
        
        -- Since the dominos are equal and the widths are equal, the tilings are equal
        -- The key is to use Sigma.ext_iff
        
        -- First, we need to show the tilings are equal after casting
        have htiling_eq : hwidth ▸ (composeTilings (m + 1) ts').2 = T := by
          apply Tiling.ext
          rw [Tiling.subst_dominos]
          exact hdominos_eq
        
        -- The goal uses raw decomposeTiling expressions instead of m and ts'
        -- We need to convert using the definitional equalities
        show composeTilings (m + 1) ts' = ⟨n' + 1, T⟩
        
        -- Use Sigma.ext_iff to construct the equality
        rw [Sigma.ext_iff]
        refine ⟨hwidth, ?_⟩
        -- Now need to show HEq (composeTilings (m + 1) ts').2 T
        -- We have: hwidth ▸ (composeTilings (m + 1) ts').2 = T
        -- Use eqRec_heq_iff_heq: (h ▸ a ≍ b) ↔ (a ≍ b)
        exact eqRec_heq_iff.mp (heq_of_eq htiling_eq)
      · -- No faults: T is faultfree
        have hff : isFaultfree (n' + 1) T := by
          constructor
          · omega
          · intro k hfault
            exact hne ⟨k, hfault⟩
        -- Show that decomposeTiling returns a singleton
        have hne' : ¬(faultPositions (n' + 1) T).Nonempty := hne
        have hdecomp : decomposeTiling (n' + 1) T = 
          ⟨1, fun _ => ⟨n' + 1, ⟨T, hff⟩⟩⟩ := by
          simp only [decomposeTiling, dite_eq_right hne']
        rw [hdecomp]
        
        -- composeTilings 1 ts = ⟨(ts 0).1, (ts 0).2.val⟩ = ⟨n' + 1, T⟩
        apply Sigma.ext (composeTilings_one_width (fun _ => ⟨n' + 1, ⟨T, hff⟩⟩))
        exact heq_of_eq (composeTilings_one_tiling (fun _ => ⟨n' + 1, ⟨T, hff⟩⟩))

/-- Decomposition is invariant under type cast (subst).
    This is key for handling dependent types in the inverse proofs. -/
theorem decomposeTiling_subst {n m : ℕ} (h : n = m) (T : Tiling (Rectangle n 2)) :
    decomposeTiling n T = decomposeTiling m (h ▸ T) := by
  subst h
  rfl

/-- Decomposition depends only on width and dominos.
    If two tilings have the same width and dominos, their decompositions are equal. -/
theorem decomposeTiling_eq_of_dominos_eq {n m : ℕ} (h : n = m) 
    (T1 : Tiling (Rectangle n 2)) (T2 : Tiling (Rectangle m 2))
    (hdom : T1.dominos = T2.dominos) :
    decomposeTiling n T1 = decomposeTiling m T2 := by
  subst h
  have hT_eq : T1 = T2 := Tiling.ext T1 T2 hdom
  rw [hT_eq]

/-- Helper lemma for proving equality of sigma types with Fin-indexed functions.
    This is used to prove decomposeTiling_composeTilings in the k ≥ 2 case. -/
theorem sigma_fin_fun_ext {α : Type*} (n m : ℕ) (h : n = m) 
    (f : Fin n → α) (g : Fin m → α)
    (hfg : ∀ i : Fin m, f ⟨i.val, by omega⟩ = g i) :
    (⟨n, f⟩ : Σ k, Fin k → α) = ⟨m, g⟩ := by
  apply Sigma.ext h
  simp only
  apply Function.hfunext (by simp only [h])
  intro i j hij
  have hi_eq : i.val = j.val := by
    have : HEq i j := hij
    cases h
    exact (Fin.heq_ext_iff rfl).mp this
  rw [heq_eq_eq]
  have hj_eq : (⟨i.val, by omega⟩ : Fin m) = j := Fin.ext hi_eq
  rw [← hj_eq]
  have hi_eq' : (⟨i.val, by omega⟩ : Fin n) = i := Fin.ext rfl
  conv_lhs => rw [← hi_eq']
  exact hfg ⟨i.val, by omega⟩

/-- Composition followed by decomposition gives back the original tuple.
    
    This theorem proves that composing faultfree tilings and then decomposing 
    recovers the original tuple of tilings.
    
    The proof handles two cases:
    1. If k = 0 (empty tuple), the composed tiling is empty (width 0), and 
       decomposeTiling returns the empty tuple by definition.
    2. If k > 0, the composed tiling has positive width, and we need to show that
       the faults in the composed tiling occur exactly at the partial width sums,
       so decomposing at those faults recovers the original pieces. -/
theorem decomposeTiling_composeTilings (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    decomposeTiling (composeTilings k ts).1 (composeTilings k ts).2 = ⟨k, ts⟩ := by
  -- Use strong induction on k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
      -- k = 0: empty tuple, composed tiling has width 0
      have hw : (composeTilings 0 ts).1 = 0 := by
        simp only [composeTilings, Finset.univ_eq_empty, Finset.sum_empty]
      rw [decomposeTiling_subst hw]
      have hdec : decomposeTiling 0 (hw ▸ (composeTilings 0 ts).2) = ⟨0, Fin.elim0⟩ := by
        unfold decomposeTiling
        rfl
      rw [hdec]
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (funext fun i => i.elim0)
    | 1 =>
      -- k = 1: single faultfree tiling
      -- The key insight: composeTilings 1 ts produces a Sigma pair where
      -- the width equals (ts 0).1 and the tiling equals (ts 0).2.val
      -- Since the original tiling is faultfree, decomposeTiling returns a singleton
      
      -- First, set up the key properties
      have hwidth : (composeTilings 1 ts).1 = (ts 0).1 := composeTilings_one_width ts
      have htiling : (composeTilings 1 ts).2 = (ts 0).2.val := composeTilings_one_tiling ts
      have hff : isFaultfree (composeTilings 1 ts).1 (composeTilings 1 ts).2 := 
        composeTilings_one_isFaultfree ts
      have hpos : (ts 0).1 > 0 := (ts 0).2.property.1
      
      -- The composed tiling equals ⟨(ts 0).1, (ts 0).2.val⟩
      have hpair : composeTilings 1 ts = ⟨(ts 0).1, (ts 0).2.val⟩ := by
        apply Sigma.ext hwidth
        exact heq_of_eq htiling
      
      -- Rewrite the goal using this equality
      rw [hpair]
      -- Goal: decomposeTiling (ts 0).1 (ts 0).2.val = ⟨1, ts⟩
      
      -- Destructure ts 0 to get the width and the faultfree tiling together
      -- This avoids the dependent type issue
      rcases hts0 : ts 0 with ⟨m, T, hT_ff⟩
      -- Now hts0 : ts 0 = ⟨m, ⟨T, hT_ff⟩⟩
      
      -- Update the goal and hypotheses using hts0
      simp only [hts0] at hpos ⊢
      -- Now hpos : m > 0
      -- Goal: decomposeTiling m T = ⟨1, ts⟩
      
      -- Since m > 0, we can write m = n + 1 for some n
      -- Use match to handle the pattern matching in decomposeTiling
      match m, T, hT_ff, hpos, hts0 with
      | n + 1, T, hT_ff, hpos, hts0 =>
        -- m = n + 1
        have hne : ¬(faultPositions (n + 1) T).Nonempty := 
          faultPositions_not_nonempty_of_isFaultfree (n + 1) T hT_ff
        
        simp only [decomposeTiling, dite_eq_right hne]
        
        -- Goal: ⟨1, fun _ => ⟨n + 1, ⟨T, _⟩⟩⟩ = ⟨1, ts⟩
        simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
        funext i
        simp only [Fin.fin_one_eq_zero]
        
        -- Show ⟨n + 1, ⟨T, _⟩⟩ = ts 0
        -- We have hts0 : ts 0 = ⟨n + 1, ⟨T, hT_ff⟩⟩
        rw [hts0]
        -- Goal is now definitionally equal
    | k' + 2 =>
      -- k = k' + 2 ≥ 2: multiple components
      -- The composed tiling has faults at the boundaries between components
      have hk_ge2 : k' + 2 ≥ 2 := by omega
      
      -- 1. There is a fault at position (ts 0).1 (the boundary after the first component)
      have hfault := composeTilings_hasFault_at_boundary (k' + 2) hk_ge2 ts
      
      -- The fault positions are nonempty
      have hne : (faultPositions (composeTilings (k' + 2) ts).1 (composeTilings (k' + 2) ts).2).Nonempty := 
        ⟨(ts ⟨0, by omega⟩).1, hfault⟩
      
      -- 2. The minimum fault is at (ts 0).1
      have hmin_eq := composeTilings_minFault_eq (k' + 2) hk_ge2 ts hne
      
      -- 3. Apply induction hypothesis to the tail
      have ih_tail := ih (k' + 1) (by omega) (faultfreeTilingsTail (k' + 2) (by omega) ts)
      
      -- 4. The width of the composed tiling is positive
      have hwidth_pos : (composeTilings (k' + 2) ts).1 > 0 := by
        have h0 : (ts ⟨0, by omega⟩).1 > 0 := (ts ⟨0, by omega⟩).2.property.1
        have hle : (ts ⟨0, by omega⟩).1 ≤ (composeTilings (k' + 2) ts).1 := by
          simp only [composeTilings]
          apply Finset.single_le_sum (s := Finset.univ) (f := fun i => (ts i).1)
            (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
        omega
      
      -- 5. Key equalities for the restrict operations
      have hleft_eq := restrictTilingLeft_composeTilings_eq (k' + 2) hk_ge2 ts hfault
      have hright_eq := restrictTilingRight_composeTilings_eq (k' + 2) hk_ge2 ts hfault
      
      -- 6. The width of the right restriction equals the tail composition width
      have hright_width := composeTilings_tail_width (k' + 2) hk_ge2 ts
      
      -- The width W = (composeTilings (k' + 2) ts).1 is positive, so W = (W - 1) + 1
      have hW_eq : (composeTilings (k' + 2) ts).1 = ((composeTilings (k' + 2) ts).1 - 1) + 1 := by omega
      
      -- Use decomposeTiling_subst to convert to the form (n + 1)
      rw [decomposeTiling_subst hW_eq]
      
      -- Now we can apply decomposeTiling_hasFault
      -- First, convert the nonemptiness proof
      have hne' : (faultPositions (((composeTilings (k' + 2) ts).1 - 1) + 1) 
          (hW_eq ▸ (composeTilings (k' + 2) ts).2)).Nonempty := by
        -- faultPositions only depends on dominos, which are preserved by subst
        simp only [faultPositions, Set.Nonempty, Set.mem_ofPred_eq]
        obtain ⟨k, hk⟩ := hne
        use k
        simp only [hasFault] at hk ⊢
        simp only [Tiling.subst_dominos]
        constructor
        · exact hk.1
        constructor
        · -- k < ((composeTilings (k' + 2) ts).1 - 1) + 1 = (composeTilings (k' + 2) ts).1
          have h := hk.2.1
          simp only [Nat.sub_add_cancel hwidth_pos] at h ⊢
          exact h
        · exact hk.2.2
      
      -- Apply the hasFault characterization
      rw [decomposeTiling_hasFault ((composeTilings (k' + 2) ts).1 - 1) 
          (hW_eq ▸ (composeTilings (k' + 2) ts).2) hne']
      
      -- Now we need to show the equality of sigma types
      -- LHS: ⟨m + 1, fun i => if i.val = 0 then ⟨minF, left⟩ else ts_right (i-1)⟩
      -- RHS: ⟨k' + 2, ts⟩
      
      -- Key: minF = (ts 0).1
      have hminF_eq : minFault (((composeTilings (k' + 2) ts).1 - 1) + 1) 
          (hW_eq ▸ (composeTilings (k' + 2) ts).2) hne' = (ts ⟨0, by omega⟩).1 := by
        -- The width ((composeTilings (k' + 2) ts).1 - 1) + 1 = (composeTilings (k' + 2) ts).1
        have hW_simp : ((composeTilings (k' + 2) ts).1 - 1) + 1 = (composeTilings (k' + 2) ts).1 := 
          Nat.sub_add_cancel hwidth_pos
        -- The two fault position sets are equal because:
        -- 1. The dominos are the same (subst preserves dominos)
        -- 2. The width bound is the same (by hW_simp)
        have hfp_eq : faultPositions (((composeTilings (k' + 2) ts).1 - 1) + 1) 
            (hW_eq ▸ (composeTilings (k' + 2) ts).2) = 
            faultPositions (composeTilings (k' + 2) ts).1 (composeTilings (k' + 2) ts).2 := by
          apply Set.ext
          intro j
          simp only [faultPositions, Set.mem_ofPred_eq, hasFault, Tiling.subst_dominos]
          constructor
          · intro ⟨h1, h2, h3⟩
            refine ⟨h1, ?_, h3⟩
            simp only [hW_simp] at h2
            exact h2
          · intro ⟨h1, h2, h3⟩
            refine ⟨h1, ?_, h3⟩
            simp only [hW_simp]
            exact h2
        -- Use the fact that the sets are equal to show the minFaults are equal
        have hfinite1 := faultPositions_finite (((composeTilings (k' + 2) ts).1 - 1) + 1) 
            (hW_eq ▸ (composeTilings (k' + 2) ts).2)
        have hfinite2 := faultPositions_finite (composeTilings (k' + 2) ts).1 
            (composeTilings (k' + 2) ts).2
        have htoFinset_eq : hfinite1.toFinset = hfinite2.toFinset := by
          ext x
          simp only [Set.Finite.mem_toFinset]
          rw [hfp_eq]
        -- minFault is defined as min' of the toFinset
        unfold minFault
        -- The min' of equal finsets is equal
        have hne1 : hfinite1.toFinset.Nonempty := by
          rw [Set.Finite.toFinset_nonempty]
          exact hne'
        have hne2 : hfinite2.toFinset.Nonempty := by
          rw [Set.Finite.toFinset_nonempty]
          exact hne
        calc hfinite1.toFinset.min' _ 
            = hfinite1.toFinset.min' hne1 := rfl
          _ = hfinite2.toFinset.min' hne2 := by simp only [htoFinset_eq]
          _ = minFault (composeTilings (k' + 2) ts).1 (composeTilings (k' + 2) ts).2 hne := rfl
          _ = (ts ⟨0, by omega⟩).1 := hmin_eq
      
      -- The proof for k >= 2 requires showing:
      -- 1. The count (m + 1) equals k' + 2
      -- 2. The 0th element equals ts 0
      -- 3. The remaining elements equal ts 1, ts 2, etc.
      
      -- Set up the width simplification
      have hW_simp : ((composeTilings (k' + 2) ts).1 - 1) + 1 = (composeTilings (k' + 2) ts).1 := 
        Nat.sub_add_cancel hwidth_pos
      
      -- The hasFault proof for the subst'd tiling, using the minFault
      have hminF' := minFault_hasFault (((composeTilings (k' + 2) ts).1 - 1) + 1) 
          (hW_eq ▸ (composeTilings (k' + 2) ts).2) hne'
      
      -- Key simplification: minFault equals (ts 0).1
      -- So we can work with (ts 0).1 directly
      
      -- The right restriction at minFault has the same width as the tail composition
      have hright_width_eq : (((composeTilings (k' + 2) ts).1 - 1) + 1) - 
          (minFault (((composeTilings (k' + 2) ts).1 - 1) + 1) (hW_eq ▸ (composeTilings (k' + 2) ts).2) hne') = 
          (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).1 := by
        rw [hminF_eq, hW_simp]
        have htail := composeTilings_tail_width (k' + 2) hk_ge2 ts
        -- htail : (composeTilings (k' + 2 - 1) (tail ts)).1 = (composeTilings (k' + 2) ts).1 - (ts 0).1
        -- We need: (composeTilings (k' + 2) ts).1 - (ts 0).1 = (composeTilings (k' + 1) (tail ts)).1
        -- Note: k' + 2 - 1 = k' + 1, so this is just htail.symm with the k simplification
        -- Use congrArg to handle the dependent type
        have hk_simp : k' + 2 - 1 = k' + 1 := by omega
        calc (composeTilings (k' + 2) ts).1 - (ts ⟨0, by omega⟩).1 
            = (composeTilings (k' + 2 - 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).1 := htail.symm
          _ = (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).1 := by
              congr 1

      -- The key insight: decomposeTiling of the right restriction equals ⟨k' + 1, tail ts⟩
      -- This follows from:
      -- 1. The right restriction equals the tail composition (after cast)
      -- 2. By ih_tail, decomposeTiling of tail composition = ⟨k' + 1, tail ts⟩
      
      -- The proof involves showing:
      -- - First component: (decomposeTiling ... right').fst + 1 = k' + 2
      --   This follows from hright_width_eq and ih_tail
      -- - Second component: the functions match
      --   For i=0: ⟨minF, left⟩ = ts 0 (by hminF_eq and hleft_eq)
      --   For i>0: ts_right(i-1) = ts i (by ih_tail and faultfreeTilingsTail definition)
      
      -- Key helper lemmas established above:
      -- - hfault: hasFault at position (ts 0).1
      -- - hne: faultPositions is nonempty
      -- - hmin_eq: minFault = (ts 0).1
      -- - ih_tail: decomposeTiling of tail composition = ⟨k' + 1, tail ts⟩
      -- - hleft_eq: left restriction = (ts 0).2.val
      -- - hright_eq: right restriction = tail composition (after cast)
      -- - hright_width_eq: width of right = width of tail composition
      
      -- Abbreviations for readability
      let n' := (composeTilings (k' + 2) ts).1 - 1
      let T' := hW_eq ▸ (composeTilings (k' + 2) ts).2
      let minF := minFault (n' + 1) T' hne'
      let hminF'' := minFault_hasFault (n' + 1) T' hne'
      let hminF_min : ∀ j, j < minF → ¬hasFault (n' + 1) T' j := fun j hj hfault => 
        absurd (minFault_le (n' + 1) T' hne' j hfault) (not_le.mpr hj)
      let left := restrictTilingLeft (n' + 1) T' minF hminF''
      let left_ff := restrictTilingLeft_isFaultfree (n' + 1) T' minF hminF'' hminF_min
      let right := restrictTilingRight (n' + 1) T' minF hminF''
      
      -- The decomposition of the right part
      let decomp_right := decomposeTiling (n' + 1 - minF) right
      
      -- Step 1: Show decomposeTiling of right equals decomposeTiling of tail composition
      -- First, we need the dominos equality
      have hright_dominos : right.dominos = 
          (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).2.dominos := by
        -- right = restrictTilingRight of the subst'd tiling
        -- The subst'd tiling has the same dominos as the original
        have hsubst_dom : T'.dominos = (composeTilings (k' + 2) ts).2.dominos := 
          Tiling.subst_dominos hW_eq (composeTilings (k' + 2) ts).2
        -- minF = (ts 0).1
        have hminF_eq' : minF = (ts ⟨0, by omega⟩).1 := hminF_eq
        -- restrictTilingRight of T' at minF has the same dominos as the original
        have hrest_dom : (restrictTilingRight (n' + 1) T' minF hminF'').dominos = 
            (restrictTilingRight (composeTilings (k' + 2) ts).1 (composeTilings (k' + 2) ts).2 
              (ts ⟨0, by omega⟩).1 hfault).dominos := by
          simp only [restrictTilingRight, hsubst_dom, hminF_eq']
        rw [hrest_dom]
        exact restrictTilingRight_composeTilings_dominos_eq (k' + 2) hk_ge2 ts hfault
      
      -- Use decomposeTiling_eq_of_dominos_eq
      have hdecomp_eq : decomp_right = 
          decomposeTiling (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).1
            (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).2 := by
        apply decomposeTiling_eq_of_dominos_eq hright_width_eq right
        exact hright_dominos
      
      -- By ih_tail, decomposeTiling of tail composition = ⟨k' + 1, tail ts⟩
      have hdecomp_tail : decomp_right = ⟨k' + 1, faultfreeTilingsTail (k' + 2) (by omega) ts⟩ := by
        rw [hdecomp_eq]
        exact ih_tail
      
      -- Step 2: First component equality
      have h_fst : decomp_right.1 + 1 = k' + 2 := by
        simp only [hdecomp_tail]
      
      -- Step 3: Apply sigma_fin_fun_ext to prove the equality
      apply sigma_fin_fun_ext (decomp_right.1 + 1) (k' + 2) h_fst
      
      -- Step 4: Prove elementwise equality
      intro i
      simp only
      -- Case split on whether i = 0
      by_cases hi : i.val = 0
      · -- Case i = 0: Show ⟨minF, ⟨left, left_ff⟩⟩ = ts 0
        simp only [hi, ↓reduceDIte]
        -- Since i.val = 0, we have i = ⟨0, _⟩
        have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi
        -- Rewrite ts i to ts ⟨0, _⟩
        conv_rhs => rw [hi_eq]
        -- Now goal is: ⟨minF, ⟨left, left_ff⟩⟩ = ts ⟨0, _⟩
        -- minF = (ts 0).1 by hminF_eq
        -- left = (ts 0).2.val (after casting by hminF_eq)
        -- 
        -- Step 1: Show left.dominos = (ts ⟨0, _⟩).2.val.dominos
        -- left = restrictTilingLeft (n' + 1) T' minF hminF''
        -- T' = hW_eq ▸ (composeTilings (k' + 2) ts).2
        -- T'.dominos = (composeTilings (k' + 2) ts).2.dominos (by Tiling.subst_dominos)
        have hT'_dominos : T'.dominos = (composeTilings (k' + 2) ts).2.dominos := 
          Tiling.subst_dominos hW_eq (composeTilings (k' + 2) ts).2
        have hleft_dominos : left.dominos = (ts ⟨0, by omega⟩).2.val.dominos := by
          simp only [left, restrictTilingLeft]
          -- left.dominos = {d ∈ T'.dominos | d.inLeftPart minF}
          -- We need to show this equals (ts ⟨0, _⟩).2.val.dominos
          -- By hleft_eq, restrictTilingLeft on the original tiling equals (ts ⟨0, _⟩).2.val
          -- So we need to connect T' to the original tiling
          have horiginal : (restrictTilingLeft (composeTilings (k' + 2) ts).1 
              (composeTilings (k' + 2) ts).2 (ts ⟨0, by omega⟩).1 hfault).dominos = 
              (ts ⟨0, by omega⟩).2.val.dominos := by
            rw [hleft_eq]
          simp only [restrictTilingLeft] at horiginal
          -- Now we need: {d ∈ T'.dominos | d.inLeftPart minF} = {d ∈ (composeTilings ...).2.dominos | d.inLeftPart (ts ⟨0, _⟩).1}
          -- Use hT'_dominos and hminF_eq
          have hminF_eq' : minF = (ts ⟨0, by omega⟩).1 := hminF_eq
          rw [hT'_dominos, hminF_eq']
          exact horiginal
        -- Step 2: Destructure ts ⟨0, _⟩ to get concrete values
        -- This allows us to use subst on the width equality
        rcases hts0 : ts ⟨0, by omega⟩ with ⟨w0, T0, hT0_ff⟩
        -- Now hts0 : ts ⟨0, _⟩ = ⟨w0, ⟨T0, hT0_ff⟩⟩
        -- hminF_eq : minF = w0
        simp only [hts0] at hminF_eq
        -- Rewrite hleft_dominos using hts0
        have hleft_dominos' : left.dominos = T0.dominos := by
          rw [hleft_dominos, hts0]
        -- Now minF = w0 and left.dominos = T0.dominos
        -- Use subst to replace minF with w0
        subst hminF_eq
        -- Now minF is replaced by w0, so left : Tiling (Rectangle w0 2)
        -- And T0 : Tiling (Rectangle w0 2) - same type!
        have hleft_val : left = T0 := Tiling.ext left T0 hleft_dominos'
        subst hleft_val
        -- Now left is replaced by T0
        -- Goal: ⟨w0, ⟨T0, left_ff⟩⟩ = ⟨w0, ⟨T0, hT0_ff⟩⟩
        rfl
      · -- Case i > 0: Show decomp_right.2 ⟨i - 1, _⟩ = ts i
        have hi_pos : i.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
        simp only [hi, ↓reduceDIte]
        -- Goal: decomp_right.2 ⟨i.val - 1, _⟩ = ts i
        -- We have hdecomp_tail : decomp_right = ⟨k' + 1, faultfreeTilingsTail (k' + 2) (by omega) ts⟩
        -- 
        -- Extract h1 : decomp_right.1 = k' + 1
        have h1 : decomp_right.1 = k' + 1 := by
          have := congrArg Sigma.fst hdecomp_tail
          simp only at this
          exact this
        -- Use Sigma.ext_iff to extract the HEq of second components
        rw [Sigma.ext_iff] at hdecomp_tail
        obtain ⟨hk, hf⟩ := hdecomp_tail
        -- hk : decomp_right.1 = k' + 1
        -- hf : HEq decomp_right.2 (faultfreeTilingsTail ...)
        -- 
        -- The key is that HEq of functions implies equality of values at HEq indices
        have hindex : HEq (⟨i.val - 1, by omega⟩ : Fin decomp_right.1) 
                          (⟨i.val - 1, by omega⟩ : Fin (k' + 1)) := by
          rw [Fin.heq_ext_iff h1]
        -- Apply congr_heq to get the equality at the specific index
        have happ := congr_heq hf hindex
        -- happ : decomp_right.2 ⟨i.val - 1, _⟩ = faultfreeTilingsTail ... ⟨i.val - 1, _⟩
        rw [happ]
        -- Goal: faultfreeTilingsTail (k' + 2) (by omega) ts ⟨i.val - 1, _⟩ = ts i
        -- By definition: faultfreeTilingsTail k hk ts j = ts ⟨j.val + 1, _⟩
        simp only [faultfreeTilingsTail]
        -- Goal: ts ⟨(i.val - 1) + 1, _⟩ = ts i
        -- Since i.val ≥ 1, we have (i.val - 1) + 1 = i.val
        congr 1
        simp only [Fin.ext_iff]
        omega


/-- The width of the composed tiling equals the sum of widths of the components.
    This follows from the definition of composeTilings as horizontal concatenation. -/
theorem composeTilings_width (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings k ts).1 = ∑ i : Fin k, (ts i).1 := by
  rfl

/-- The sum of widths of the faultfree tilings equals the width of the original.
    This is the key property that makes the decomposition weight-preserving. -/
theorem decomposeTiling_weight_sum (n : ℕ) (T : Tiling (Rectangle n 2)) :
    let ⟨k, ts⟩ := decomposeTiling n T
    (∑ i : Fin k, (ts i).1) = n := by
  simp only
  have h1 := composeTilings_decomposeTiling n T
  simp only at h1
  have h2 := composeTilings_width (decomposeTiling n T).1 (decomposeTiling n T).2
  rw [← h2]
  exact congrArg Sigma.fst h1

/-- Main decomposition isomorphism (Lemma \ref{lem.gf.weighted-set.domino.fd}):
    
    Any domino tiling of a height-2 rectangle can be decomposed **uniquely** into a 
    tuple of faultfree tilings of (usually smaller) height-2 rectangles, by cutting 
    it along its faults.
    
    This gives an isomorphism of weighted sets:
      D ≅ F⁰ + F¹ + F² + F³ + ...
    where D = TilingsHeight2 and F = FaultfreeTilingsHeight2.
    
    The isomorphism preserves weights: the sum of the widths of the faultfree tilings
    in the tuple equals the width of the original tiling. -/
def tiling_decomposition_isomorphism :
    WeightedSet.Isomorphism TilingsHeight2 FaultfreeTilingsHeight2.tuples where
  toEquiv := {
    toFun := fun ⟨n, T⟩ => decomposeTiling n T
    invFun := fun ⟨k, ts⟩ => composeTilings k ts
    left_inv := fun ⟨n, T⟩ => composeTilings_decomposeTiling n T
    right_inv := fun ⟨k, ts⟩ => decomposeTiling_composeTilings k ts
  }
  weight_eq := fun ⟨n, T⟩ => by
    simp only [WeightedSet.tuples, TilingsHeight2]
    exact decomposeTiling_weight_sum n T
/-! #### Helper definitions for the Fibonacci recurrence bijection -/


/-- Prepend a vertical domino to a tiling of Rectangle m 2, giving a tiling of Rectangle (m+1) 2.
    
    The new tiling has dominos = {vertical 1 1} ∪ (T.dominos shifted right by 1).
    This is the inverse of restricting at fault 1 when a vertical domino is present. -/
def prependVertical (m : ℕ) (T : Tiling (Rectangle m 2)) : Tiling (Rectangle (m + 1) 2) where
  dominos := {Domino.vertical 1 1} ∪ T.dominos.image (fun d => d.shiftNat 1)
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image] at hd1 hd2
    rcases hd1 with rfl | ⟨d1', hd1', rfl⟩ <;> rcases hd2 with rfl | ⟨d2', hd2', rfl⟩
    · exact (hne rfl).elim
    · -- vertical 1 1 vs shifted d2'
      -- vertical 1 1 covers column 1, shifted dominos cover columns ≥ 2
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift]
      rw [Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
      cases d2' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs vertical 1 1
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift]
      rw [Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
      cases d1' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs shifted d2'
      have hne' : d1' ≠ d2' := by
        intro heq; subst heq; exact hne rfl
      have hdisj := T.pairwise_disjoint hd1' hd2' hne'
      simp only [Function.onFun, Domino.shiftNat_toShape]
      exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
        simp only [Prod.mk.injEq] at h; ext <;> omega) hdisj
  cover := by
    ext ⟨x, y⟩
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_image,
               Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro ⟨d, hd, hp⟩
      rcases hd with rfl | ⟨d', hd', rfl⟩
      · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
        rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
      · have hd'_rect := domino_subset_rect m T d' hd'
        rw [Domino.shiftNat_toShape] at hp
        obtain ⟨⟨x', y'⟩, hp', heq⟩ := hp
        simp only [Prod.mk.injEq] at heq
        have hxy' := hd'_rect hp'
        simp only [Rectangle, Set.mem_ofPred_eq] at hxy'
        omega
    · intro ⟨hx1, hx2, hy1, hy2⟩
      rcases (show x = 1 ∨ x ≥ 2 by omega) with rfl | hx_ge2
      · -- x = 1: covered by vertical 1 1
        use Domino.vertical 1 1, Or.inl rfl
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        have hy12 : y = 1 ∨ y = 2 := by omega
        rcases hy12 with rfl | rfl <;> simp
      · -- x ≥ 2: covered by shifted domino
        have hxy_rect : (x - 1, y) ∈ Rectangle m 2 := by
          simp only [Rectangle, Set.mem_ofPred_eq]
          omega
        rw [← T.cover] at hxy_rect
        simp only [Set.mem_iUnion] at hxy_rect
        obtain ⟨d', hd', hp'⟩ := hxy_rect
        use d'.shiftNat 1, Or.inr ⟨d', hd', rfl⟩
        rw [Domino.shiftNat_toShape]
        refine ⟨(x - 1, y), hp', ?_⟩
        simp only [Prod.mk.injEq]
        constructor <;> first | ring | trivial

/-- Prepend a pair of horizontal dominos to a tiling of Rectangle m 2, giving a tiling of Rectangle (m+2) 2.
    
    The new tiling has dominos = {horizontal 1 1, horizontal 1 2} ∪ (T.dominos shifted right by 2).
    This is the inverse of restricting at fault 2 when horizontal dominos are present. -/
def prependHorizontalPair (m : ℕ) (T : Tiling (Rectangle m 2)) : Tiling (Rectangle (m + 2) 2) where
  dominos := {Domino.horizontal 1 1, Domino.horizontal 1 2} ∪ T.dominos.image (fun d => d.shiftNat 2)
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image] at hd1 hd2
    rcases hd1 with (rfl | rfl) | ⟨d1', hd1', rfl⟩ <;> rcases hd2 with (rfl | rfl) | ⟨d2', hd2', rfl⟩
    · exact (hne rfl).elim
    · -- horizontal 1 1 vs horizontal 1 2
      simp only [Function.onFun, Domino.toShape, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1 hx2
      rcases hx1 with ⟨_, hy1⟩ | ⟨_, hy1⟩ <;> rcases hx2 with ⟨_, hy2⟩ | ⟨_, hy2⟩ <;> omega
    · -- horizontal 1 1 vs shifted d2'
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
      cases d2' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- horizontal 1 2 vs horizontal 1 1
      simp only [Function.onFun, Domino.toShape, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1 hx2
      rcases hx1 with ⟨_, hy1⟩ | ⟨_, hy1⟩ <;> rcases hx2 with ⟨_, hy2⟩ | ⟨_, hy2⟩ <;> omega
    · exact (hne rfl).elim
    · -- horizontal 1 2 vs shifted d2'
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
      cases d2' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs horizontal 1 1
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
      cases d1' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs horizontal 1 2
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
      cases d1' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs shifted d2'
      have hne' : d1' ≠ d2' := by
        intro heq; subst heq; exact hne rfl
      have hdisj := T.pairwise_disjoint hd1' hd2' hne'
      simp only [Function.onFun, Domino.shiftNat_toShape]
      exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
        simp only [Prod.mk.injEq] at h; ext <;> omega) hdisj
  cover := by
    ext ⟨x, y⟩
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, 
               Set.mem_image, Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro ⟨d, hd, hp⟩
      rcases hd with (rfl | rfl) | ⟨d', hd', rfl⟩
      · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
        rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
      · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
        rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
      · have hd'_rect := domino_subset_rect m T d' hd'
        rw [Domino.shiftNat_toShape] at hp
        obtain ⟨⟨x', y'⟩, hp', heq⟩ := hp
        simp only [Prod.mk.injEq] at heq
        have hxy' := hd'_rect hp'
        simp only [Rectangle, Set.mem_ofPred_eq] at hxy'
        omega
    · intro ⟨hx1, hx2, hy1, hy2⟩
      have hy12 : y = 1 ∨ y = 2 := by omega
      rcases (show x = 1 ∨ x = 2 ∨ x ≥ 3 by omega) with rfl | rfl | hx_ge3
      · -- x = 1: covered by horizontal 1 y
        rcases hy12 with rfl | rfl
        · use Domino.horizontal 1 1, Or.inl (Or.inl rfl)
          simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          left; trivial
        · use Domino.horizontal 1 2, Or.inl (Or.inr rfl)
          simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          left; trivial
      · -- x = 2: covered by horizontal 1 y
        rcases hy12 with rfl | rfl
        · use Domino.horizontal 1 1, Or.inl (Or.inl rfl)
          simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          right; trivial
        · use Domino.horizontal 1 2, Or.inl (Or.inr rfl)
          simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          right; trivial
      · -- x ≥ 3: covered by shifted domino
        have hxy_rect : (x - 2, y) ∈ Rectangle m 2 := by
          simp only [Rectangle, Set.mem_ofPred_eq]
          omega
        rw [← T.cover] at hxy_rect
        simp only [Set.mem_iUnion] at hxy_rect
        obtain ⟨d', hd', hp'⟩ := hxy_rect
        use d'.shiftNat 2, Or.inr ⟨d', hd', rfl⟩
        rw [Domino.shiftNat_toShape]
        refine ⟨(x - 2, y), hp', ?_⟩
        simp only [Prod.mk.injEq]
        constructor <;> first | ring | trivial
/-! #### Height-3 Rectangle Tilings -/


/-- The set of dominos that fit within a rectangle -/
def DominosInRectangle (n m : ℕ) : Set Domino :=
  {d | d.toShape ⊆ Rectangle n m}

end DominoTilingsZ
