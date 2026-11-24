module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.SAW
public import Theorem.StatisticalMechanics.Code.Universality.TriLattice.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


def triDropLast {n : ℕ} (w : Fin (n + 1) → TriStep) : Fin n → TriStep :=
  fun i => w i.castSucc


end StatMech.Universality
