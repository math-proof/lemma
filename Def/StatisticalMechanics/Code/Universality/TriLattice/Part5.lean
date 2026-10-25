/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Theorem.StatisticalMechanics.Code.Universality.TriLattice.Part4


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


def triPart1 {m n : ℕ} (w : Fin (m + n) → TriStep) : Fin m → TriStep :=
  fun i => w ⟨i, by omega⟩


def triPart2 {m n : ℕ} (w : Fin (m + n) → TriStep) : Fin n → TriStep :=
  fun i => w ⟨m + i, by omega⟩

end StatMech.Universality
