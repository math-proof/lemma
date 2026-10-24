/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace OeisA108081

open Nat


def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (n + k - 1).choose k * fib (n - k + 1)


abbrev Word := List ℤ


def l (w : Word) : Word :=
  w.reverse.map (fun x => x - 1)


def r (w : Word) : Word :=
  w.reverse.map (fun x => x + 1)

@[simp] lemma length_l (w : Word) : (l w).length = w.length := by
  simp [l]

@[simp] lemma length_r (w : Word) : (r w).length = w.length := by
  simp [r]

@[simp] lemma l_r (w : Word) : l (r w) = w := by
  simp [l, r, List.map_reverse, Function.comp_def]

@[simp] lemma r_l (w : Word) : r (l w) = w := by
  simp [l, r, List.map_reverse, Function.comp_def]


inductive XWord : Word → Prop
  | base : XWord [0]
  | step_left {u v : Word} (hu : XWord u) (hv : XWord v) : XWord (l u ++ v)
  | step_right {u v : Word} (hu : XWord u) (hv : XWord v) : XWord (u ++ r v)


def leftChild (z : ℤ) : ℤ := if Even z then z - 1 else z + 1

def rightChild (z : ℤ) : ℤ := if Even z then z + 1 else z - 1


inductive Expand : Word → Word → Prop
  | left (p s : Word) (z : ℤ) :
      Expand (p ++ z :: s) (p ++ leftChild z :: z :: s)
  | right (p s : Word) (z : ℤ) :
      Expand (p ++ z :: s) (p ++ z :: rightChild z :: s)


abbrev EdgeCoord := ℤ × Bool

def edgeValue (q : EdgeCoord) : ℤ :=
  2 * q.1 - if q.2 then 1 else 0

def edgeCoord (z : ℤ) : EdgeCoord :=
  if h : Even z then (z / 2, false) else ((z + 1) / 2, true)

@[simp] lemma edgeValue_edgeCoord (z : ℤ) : edgeValue (edgeCoord z) = z := by
  simp only [edgeCoord]
  split_ifs with h
  · obtain ⟨k, hk⟩ := h
    simp only [edgeValue, Bool.false_eq_true, ↓reduceIte]
    omega
  · have ho : Odd z := Int.not_even_iff_odd.mp h
    obtain ⟨k, hk⟩ := ho
    simp only [edgeValue, ↓reduceIte]
    omega

@[simp] lemma edgeCoord_edgeValue (q : EdgeCoord) : edgeCoord (edgeValue q) = q := by
  rcases q with ⟨k, e⟩
  cases e <;> simp [edgeCoord, edgeValue]


def edgeEquiv : EdgeCoord ≃ ℤ where
  toFun := edgeValue
  invFun := edgeCoord
  left_inv := edgeCoord_edgeValue
  right_inv := edgeValue_edgeCoord

@[simp] lemma leftChild_edgeValue_false (k : ℤ) :
    leftChild (edgeValue (k, false)) = edgeValue (k, true) := by
  have h : Even (2 * k) := ⟨k, by ring⟩
  simp [leftChild, edgeValue, h]

@[simp] lemma leftChild_edgeValue_true (k : ℤ) :
    leftChild (edgeValue (k, true)) = edgeValue (k, false) := by
  have h : ¬ Even (2 * k - 1) := by
    rw [Int.not_even_iff_odd]
    exact ⟨k - 1, by ring⟩
  simp [leftChild, edgeValue, h]

@[simp] lemma rightChild_edgeValue_false (k : ℤ) :
    rightChild (edgeValue (k, false)) = edgeValue (k + 1, true) := by
  have h : Even (2 * k) := ⟨k, by ring⟩
  simp [rightChild, edgeValue, h]
  ring

@[simp] lemma rightChild_edgeValue_true (k : ℤ) :
    rightChild (edgeValue (k, true)) = edgeValue (k - 1, false) := by
  have h : ¬ Even (2 * k - 1) := by
    rw [Int.not_even_iff_odd]
    exact ⟨k - 1, by ring⟩
  simp [rightChild, edgeValue, h]
  ring

def coordLeft : EdgeCoord → EdgeCoord
  | (k, false) => (k, true)
  | (k, true) => (k, false)

def coordRight : EdgeCoord → EdgeCoord
  | (k, false) => (k + 1, true)
  | (k, true) => (k - 1, false)


def coordWord (w : Word) : List EdgeCoord := w.map edgeCoord

@[simp] lemma map_edgeValue_coordWord (w : Word) :
    (coordWord w).map edgeValue = w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      change edgeValue (edgeCoord x) :: (coordWord xs).map edgeValue = x :: xs
      simp [ih]

@[simp] lemma coordWord_map_edgeValue (w : List EdgeCoord) :
    coordWord (w.map edgeValue) = w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      change edgeCoord (edgeValue x) :: coordWord (xs.map edgeValue) = x :: xs
      simp [ih]

@[simp] lemma edgeValue_coordLeft (q : EdgeCoord) :
    edgeValue (coordLeft q) = leftChild (edgeValue q) := by
  rcases q with ⟨k, e⟩
  cases e <;> simp [coordLeft]

@[simp] lemma edgeValue_coordRight (q : EdgeCoord) :
    edgeValue (coordRight q) = rightChild (edgeValue q) := by
  rcases q with ⟨k, e⟩
  cases e <;> simp [coordRight]

@[simp] lemma edgeCoord_leftChild (z : ℤ) :
    edgeCoord (leftChild z) = coordLeft (edgeCoord z) := by
  apply (Equiv.injective edgeEquiv)
  simp [edgeEquiv]

@[simp] lemma edgeCoord_rightChild (z : ℤ) :
    edgeCoord (rightChild z) = coordRight (edgeCoord z) := by
  apply (Equiv.injective edgeEquiv)
  simp [edgeEquiv]


inductive CoordExpand : List EdgeCoord → List EdgeCoord → Prop
  | left (p s : List EdgeCoord) (q : EdgeCoord) :
      CoordExpand (p ++ q :: s) (p ++ coordLeft q :: q :: s)
  | right (p s : List EdgeCoord) (q : EdgeCoord) :
      CoordExpand (p ++ q :: s) (p ++ q :: coordRight q :: s)


def XInsert (w : Word) : Prop := Relation.ReflTransGen Expand [0] w


def CoordInsert (w : List EdgeCoord) : Prop :=
  Relation.ReflTransGen CoordExpand [(0, false)] w


inductive CoordForest (root : EdgeCoord) : List EdgeCoord → Prop
  | nil : CoordForest root []
  | cons {u v : List EdgeCoord} :
      Relation.ReflTransGen CoordExpand [root] u →
      CoordForest root v → CoordForest root (u ++ v)


def rightIndex (q : EdgeCoord) : ℤ := q.1 - if q.2 then 1 else 0


def CoordAdjacent (q r : EdgeCoord) : Prop :=
  r.1 = q.1 ∨ r.1 = rightIndex q ∨ r.1 = rightIndex q + 1

inductive CoordPath : List EdgeCoord → Prop
  | nil : CoordPath []
  | singleton (q : EdgeCoord) : CoordPath [q]
  | cons {q r : EdgeCoord} {s : List EdgeCoord}
      (hqr : CoordAdjacent q r) (hrs : CoordPath (r :: s)) :
      CoordPath (q :: r :: s)


def CoordForestForm (root : EdgeCoord) (w : List EdgeCoord) : Prop :=
  w = [] ∨
    CoordPath w ∧ (w.head?.map Prod.fst = some root.1) ∧
      (w.getLast?.map rightIndex = some (rightIndex root))

lemma XInsert.base : XInsert [0] := Relation.ReflTransGen.refl


def xN (n : ℕ) : Set Word :=
  {w : Word | XWord w ∧ w.length = n}


def coordXN (n : ℕ) : Set (List EdgeCoord) :=
  {w | CoordInsert w ∧ w.length = n}


def bitStep (k : ℤ) (e y : Bool) : ℤ :=
  if e = y then if e then k - 1 else k + 1 else k


def bitsToCoords : ℤ → List Bool → List EdgeCoord
  | _, [] => []
  | k, e :: bs => (k, e) :: match bs with
    | [] => []
    | y :: cs => bitsToCoords (bitStep k e y) cs

@[simp] lemma bitsToCoords_cons (k : ℤ) (e : Bool) (b : List Bool) :
    bitsToCoords k (e :: b) = (k, e) :: match b with
      | [] => []
      | y :: cs => bitsToCoords (bitStep k e y) cs := by
  cases b <;> rfl


def ForestBits (m : ℕ) : Set (List Bool) :=
  {b | b.length = 2 * m + 1 ∧ b.count true = m}


def coordMovementBit (q r : EdgeCoord) : Bool :=
  if r.1 = q.1 then !q.2 else q.2


def coordsToBits : List EdgeCoord → List Bool
  | [] => []
  | [q] => [q.2]
  | q :: r :: s => q.2 :: coordMovementBit q r :: coordsToBits (r :: s)


def subsetBits (N : ℕ) (s : Finset (Fin N)) : List Bool :=
  List.ofFn (fun i => decide (i ∈ s))

@[simp] lemma length_subsetBits (N : ℕ) (s : Finset (Fin N)) :
    (subsetBits N s).length = N := by simp [subsetBits]


def coordForestXN (m : ℕ) : Set (List EdgeCoord) :=
  {w | CoordForestForm (0, false) w ∧ w.length = m + 1}


def TreeBits (m : ℕ) : Set (List Bool) :=
  coordsToBits '' coordXN (m + 1)


def CoordTree (root : EdgeCoord) (w : List EdgeCoord) : Prop :=
  Relation.ReflTransGen CoordExpand [root] w

lemma CoordForest.singleton (root : EdgeCoord) : CoordForest root [root] := by
  simpa using CoordForest.cons (Relation.ReflTransGen.refl : CoordTree root [root])
    (CoordForest.nil : CoordForest root [])


def CoordRootDecomp (root : EdgeCoord) (w : List EdgeCoord) : Prop :=
  ∃ L R, CoordForest (coordLeft root) L ∧ CoordForest (coordRight root) R ∧
    w = L ++ root :: R


def BitBalanced (b : List Bool) : Prop := 2 * b.count true = b.length


def CenteredTreeBits (m : ℕ) : Set (List Bool) :=
  {b | b ∈ ForestBits m ∧ ∃ p s,
    false :: b ++ [false] = p ++ [false, false, false] ++ s ∧
    BitBalanced p ∧ BitBalanced s}


def CrossingFree (p : List Bool) : Prop :=
  ∀ q t, p = q ++ [false, false, false] ++ t → ¬ BitBalanced q

def FirstCrossingPrefix (E p : List Bool) : Prop :=
  BitBalanced p ∧ (∃ s, E = p ++ [false, false, false] ++ s) ∧
    ∀ q t, E = q ++ [false, false, false] ++ t →
      BitBalanced q → p.length ≤ q.length

def stripEnds (b : List Bool) : List Bool := b.tail.dropLast


def CanonicalPairs (m : ℕ) : Set (List Bool × List Bool) :=
  {ps | BitBalanced ps.1 ∧ BitBalanced ps.2 ∧
    ps.1.length + ps.2.length = 2 * m ∧
    (ps.1 = [] ∨ ps.1.head? = some false) ∧
    (ps.2 = [] ∨ ps.2.getLast? = some false) ∧
    FirstCrossingPrefix (ps.1 ++ [false, false, false] ++ ps.2) ps.1}

def canonicalGlue (ps : List Bool × List Bool) : List Bool :=
  stripEnds (ps.1 ++ [false, false, false] ++ ps.2)

def WeightBits (N K : ℕ) : Set (List Bool) :=
  {b | b.length = N ∧ b.count true = K}

def PrefixBits (j : ℕ) : Set (List Bool) :=
  {p | p.length = 2 * j ∧ BitBalanced p ∧
    (p = [] ∨ p.head? = some false) ∧ CrossingFree p}

def SuffixBits (k : ℕ) : Set (List Bool) :=
  {s | s.length = 2 * k ∧ BitBalanced s ∧
    (s = [] ∨ s.getLast? = some false)}

def AllPrefixBits (j : ℕ) : Set (List Bool) :=
  {p | p.length = 2 * j ∧ BitBalanced p ∧
    (p = [] ∨ p.head? = some false)}

def BadPairs (j : ℕ) : Set (List Bool × List Bool) :=
  ⋃ r : Fin (j + 1),
    {qt : List Bool × List Bool | qt.1 ∈ PrefixBits r ∧
      qt.2 ∈ WeightBits (2 * (j - r) - 3) (j - r) ∧ 3 ≤ j - r}

def badGlue (qt : List Bool × List Bool) : List Bool :=
  qt.1 ++ [false, false, false] ++ qt.2


noncomputable def suffixSeries : PowerSeries ℕ :=
  PowerSeries.mk (fun n => (2 * n - 1).choose n)

noncomputable def badSeries : PowerSeries ℕ :=
  PowerSeries.X ^ 3 *
    (suffixSeries * PowerSeries.catalanSeries ^ 4)

noncomputable def prefixSeries : PowerSeries ℕ :=
  PowerSeries.mk (fun n => (PrefixBits n).ncard)

noncomputable def catalanTreeSeries : PowerSeries ℕ :=
  PowerSeries.X * PowerSeries.catalanSeries

noncomputable def treeCountSeries : PowerSeries ℕ :=
  prefixSeries * suffixSeries

noncomputable def treeStepSeries : PowerSeries ℕ :=
  catalanTreeSeries + catalanTreeSeries ^ 2

noncomputable def geomStepPolynomial (m : ℕ) : Polynomial ℕ :=
  ∑ i ∈ Finset.range (m + 1),
    (Polynomial.X + Polynomial.X ^ 2) ^ i

noncomputable def fibPolynomial (m : ℕ) : Polynomial ℕ :=
  ∑ r ∈ Finset.range (m + 1),
    Polynomial.C (fib (r + 1)) * Polynomial.X ^ r

noncomputable def fibTreePartialSeries (m : ℕ) : PowerSeries ℕ :=
  ∑ r ∈ Finset.range (m + 1),
    PowerSeries.C (fib (r + 1)) * catalanTreeSeries ^ r

def CoordLeftSide (root q : EdgeCoord) : Prop :=
  if root.2 then root.1 ≤ q.1 else q.1 ≤ root.1

def CoordRightSide (root q : EdgeCoord) : Prop :=
  if root.2 then q.1 < root.1 else root.1 < q.1
