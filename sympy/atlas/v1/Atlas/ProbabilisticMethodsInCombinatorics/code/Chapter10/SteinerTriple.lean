/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/SteinerTriple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory Filter Topology Real Set

noncomputable section

/-- A Steiner triple system on $\alpha$ (Definition 10.2.8): a collection of 3-element subsets
("triples") such that every pair of distinct elements is contained in exactly one triple. -/
structure SteinerTripleSystem (α : Type*) [DecidableEq α] where
  triples : Set (Finset α)
  triple_card : ∀ t ∈ triples, t.card = 3
  pair_in_unique_triple : ∀ (a b : α), a ≠ b →
    ∃! t, t ∈ triples ∧ a ∈ t ∧ b ∈ t

/-- Finiteness of the type of Steiner triple systems on $\{0,\dots,n-1\}$. -/
instance (n : ℕ) : Empty.Finite (SteinerTripleSystem (Fin n)) :=
  Empty.Finite.of_injective (fun s => s.triples) (fun s1 s2 h => by cases s1; cases s2; congr)

/-- The number of Steiner triple systems on $\{0,\dots,n-1\}$, denoted $\mathrm{STS}(n)$. -/
noncomputable def numSTS (n : ℕ) : ℕ :=
  Nat.card (SteinerTripleSystem (Fin n))
