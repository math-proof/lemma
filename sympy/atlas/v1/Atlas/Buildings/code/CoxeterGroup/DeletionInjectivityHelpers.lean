/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivityHelpers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterSystemFromDeletion
import Mathlib.GroupTheory.Coxeter.Basic

open CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- The product $g(k) \cdot g(k+1) \cdots g(k + m - 1)$ of $m$ consecutive
values of a sequence $g : \mathbb{N} \to W$ starting at index $k$. -/
def consecProd {W : Type*} [Monoid W] (g : ℕ → W) (k m : ℕ) : W :=
  ((List.range m).map (fun i => g (k + i))).prod

/-- Cyclic extension of $\mathtt{gen}\circ\mathtt{word}$ to all of
$\mathbb{N}$: at index $k$ it returns the generator at position $k \bmod n$. -/
def wordCyclicGen (gen : B → W) (word : List B) (n : ℕ)
    (hn : word.length = n) (hn0 : n > 0) (k : ℕ) : W :=
  gen (word.get ⟨k % n, by rw [hn]; exact Nat.mod_lt k hn0⟩)
