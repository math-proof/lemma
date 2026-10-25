/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
open Set
open SimpleGraph


namespace StatMech

namespace Lattice

theorem sw_adj_horizSucc (y x : ℤ) :
    (hypercubicLattice 2).Adj ![x, y] ![x + 1, y] := by
  rw [hypercubicLattice_adj]; simp [Fin.sum_univ_two]


theorem sw_adj_vertSucc (x y : ℤ) :
    (hypercubicLattice 2).Adj ![x, y] ![x, y + 1] := by
  rw [hypercubicLattice_adj]; simp [Fin.sum_univ_two]


end Lattice
end StatMech
