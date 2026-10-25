/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk
open Set
open SimpleGraph


namespace StatMech

namespace Lattice

def sw_horizR (y x0 : ℤ) :
    (n : ℕ) → (hypercubicLattice 2).Walk ![x0, y] ![x0 + (n : ℤ), y]
  | 0 => Walk.nil.copy rfl (by norm_num)
  | (n + 1) =>
      (sw_horizR y x0 n).append
        ((Walk.cons (sw_adj_horizSucc y (x0 + (n : ℤ))) Walk.nil).copy rfl
          (by norm_num [add_assoc]))


def sw_vertU (x y0 : ℤ) :
    (n : ℕ) → (hypercubicLattice 2).Walk ![x, y0] ![x, y0 + (n : ℤ)]
  | 0 => Walk.nil.copy rfl (by norm_num)
  | (n + 1) =>
      (sw_vertU x y0 n).append
        ((Walk.cons (sw_adj_vertSucc x (y0 + (n : ℤ))) Walk.nil).copy rfl
          (by norm_num [add_assoc]))


end Lattice
end StatMech
