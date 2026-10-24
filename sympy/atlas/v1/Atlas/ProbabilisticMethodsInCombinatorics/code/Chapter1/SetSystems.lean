/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/SetSystems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.GroupTheory.Perm.Basic

open Finset Nat

namespace SetSystems

/-- The image under a permutation `σ` of $\{0, 1, \ldots, k-1\}$: the first `k` elements
of $[n]$ in the order induced by `σ`. -/
def initialSegment {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin n => i.val < k)).image σ
