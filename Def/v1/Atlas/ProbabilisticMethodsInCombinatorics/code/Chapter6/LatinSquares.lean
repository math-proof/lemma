/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/LatinSquares.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.LatinSquares
set_option maxHeartbeats 400000

open Function


namespace LatinSquares

/-- An $n \times n$ array $L$ has a Latin transversal if there exists a permutation $\sigma$ of $\text{Fin}\ n$ such that the diagonal entries $L_{i,\sigma(i)}$ are all distinct. -/
def HasLatinTransversal {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), Injective (fun i => L i (σ i))

end LatinSquares

open LatinSquares


/-- Ryser's conjecture: every $n \times n$ Latin square with $n$ odd has a Latin transversal. -/

namespace LatinSquares

/-- The set of symbols appearing on the diagonal selected by the permutation $\sigma$, i.e. $\{L_{i,\sigma(i)} : i \in \text{Fin}\ n\}$. -/
noncomputable def transversalSymbols {n : ℕ} (L : Fin n → Fin n → Fin n)
    (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.image (fun i => L i (σ i))

end LatinSquares

/-- Ryser–Brualdi–Stein conjecture: every $n \times n$ Latin square with $n$ even admits a permutation $\sigma$ such that the diagonal $\{L_{i,\sigma(i)}\}$ contains at least $n-1$ distinct symbols (a near-transversal). -/

namespace ErdosSpencer

open Finset Real

open LatinSquares in


/-- The number of cells of the array $L$ whose entry equals the symbol $c$, i.e. $|\{(i,j) : L_{i,j} = c\}|$. -/
def symbolCount {n : ℕ} {α : Type*} [DecidableEq α]
    (L : Fin n → Fin n → α) (c : α) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => L p.1 p.2 = c)).card

/-- Generalised notion of a Latin transversal for an array with entries in an arbitrary type $\alpha$: a permutation $\sigma$ such that the selected diagonal entries $L_{i,\sigma(i)}$ are all distinct. -/
def HasLatinTransversalGen {n : ℕ} {α : Type*} (L : Fin n → Fin n → α) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), Injective (fun i => L i (σ i))

/-- The finite set of permutations $\sigma$ that yield a Latin transversal of $L$: distinct rows pick distinct symbols. -/
def goodPerms {n : ℕ} {α : Type*} [DecidableEq α] (L : Fin n → Fin n → α) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => ∀ i₁ i₂ : Fin n, i₁ ≠ i₂ → L i₁ (σ i₁) ≠ L i₂ (σ i₂))

end ErdosSpencer
