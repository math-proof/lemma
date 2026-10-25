/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Theorem.StatisticalMechanics.Code.Universality.TriLattice


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


def triPosStep (c : Fin 3) : TriStep :=
  match c with
  | 0 => 0 | 1 => 2 | 2 => 4


def triPhi (p : TriSite) : ℤ := 2 * p 0 + p 1


end StatMech.Universality
