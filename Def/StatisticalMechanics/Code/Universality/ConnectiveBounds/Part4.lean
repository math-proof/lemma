/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Theorem.StatisticalMechanics.Code.Universality.ConnectiveBounds.Part3


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


def zdPart1 {d m n : ℕ} (w : Fin (m + n) → ZdStep d) : Fin m → ZdStep d :=
  fun i => w ⟨i, by omega⟩


def zdPart2 {d m n : ℕ} (w : Fin (m + n) → ZdStep d) : Fin n → ZdStep d :=
  fun i => w ⟨m + i, by omega⟩

end StatMech.Universality
