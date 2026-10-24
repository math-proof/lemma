/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/RamseyLowerBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
namespace RamseyLowerBound

open Finset Fintype

/-- An edge of the complete graph $K_n$: an unordered, non-diagonal pair of vertices. -/
abbrev Edge (n : ℕ) := {e : Sym2 (Fin n) // ¬e.IsDiag}

/-- `edgesWithin n S` is the set of edges of $K_n$ whose endpoints both lie in `S`. -/
def edgesWithin (n : ℕ) (S : Finset (Fin n)) : Finset (Edge n) :=
  Finset.univ.filter (fun e => e.val ∈ S.sym2)

/-- Equivalence between Boolean labellings of $\alpha$ that are constantly $b$ on $s$
and arbitrary Boolean labellings of the complement $\{x : \alpha \mid x \notin s\}$. -/
noncomputable def constrainedEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : Bool) :
    {f : α → Bool // ∀ x ∈ s, f x = b} ≃ ({x : α // x ∉ s} → Bool) where
  toFun f := fun ⟨x, hx⟩ => f.val x
  invFun g := ⟨fun x => if h : x ∈ s then b else g ⟨x, h⟩,
    by intro x hx; simp [hx]⟩
  left_inv := by
    intro ⟨f, hf⟩; simp only [Subtype.mk.injEq]; ext x
    by_cases h : x ∈ s
    · simp [h, hf x h]
    · simp [h]
  right_inv := by intro g; ext ⟨x, hx⟩; simp [hx]

/-- The simple graph on $[n]$ whose edges are those colored `true` by a given 2-coloring
`c` of $K_n$. -/
noncomputable def coloringToGraph {n : ℕ} (c : Edge n → Bool) :
    SimpleGraph (Fin n) where
  Adj v w :=
    if h : v = w then False
    else c ⟨s(v, w), by rw [Sym2.mk_isDiag_iff]; exact h⟩ = true
  symm v w := by
    simp only; split_ifs with h1 h2 h2
    · exact id
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · intro hc; convert hc using 2; congr 1; exact Sym2.eq_swap
  loopless := ⟨fun v h => by simp at h⟩
