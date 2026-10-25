/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
open Finset BigOperators


namespace UnbalancingLights

/-- Conversion from booleans to signs $\{-1, +1\}$: `true ↦ 1`, `false ↦ -1`. -/
def boolToSign (b : Bool) : ℤ := if b then 1 else -1

/-- A vector $v : \mathrm{Fin}\,n \to \mathbb{Z}$ is a sign vector if every entry is
$\pm 1$. -/
def IsSignVec {n : ℕ} (v : Fin n → ℤ) : Prop := ∀ i, v i = 1 ∨ v i = -1

/-- A matrix $a : \mathrm{Fin}\,m \times \mathrm{Fin}\,n \to \mathbb{Z}$ is a sign matrix
if every entry is $\pm 1$. -/
def IsSignMatrix {m n : ℕ} (a : Fin m → Fin n → ℤ) : Prop := ∀ i j, a i j = 1 ∨ a i j = -1

/-- Total Rademacher absolute expectation: $\sum_{y \in \{-1,+1\}^n} \left|
\sum_j y_j \right|$, i.e., the (unnormalized) expected absolute value of a
$\pm 1$ random walk of length $n$. -/
def rademacherAbsExpect (n : ℕ) : ℤ :=
  ∑ y : Fin n → Bool, |∑ j : Fin n, boolToSign (y j)|

/-- Coordinate-wise sign flip on Boolean vectors: flip $y_j$ exactly when $a_j = -1$. -/
def signFlip {n : ℕ} (a : Fin n → ℤ) (y : Fin n → Bool) : Fin n → Bool :=
  fun j => decide (a j = -1) ^^ y j

end UnbalancingLights
