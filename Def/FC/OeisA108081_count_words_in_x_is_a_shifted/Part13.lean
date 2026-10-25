/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OeisA108081_count_words_in_x_is_a_shifted.Part8


namespace OeisA108081

open Nat


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

end OeisA108081
