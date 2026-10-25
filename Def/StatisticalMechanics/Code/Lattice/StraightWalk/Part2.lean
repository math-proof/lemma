/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part2
open Set
open SimpleGraph


namespace StatMech

namespace Lattice

noncomputable def sw_horizSeg (y x0 x1 : ℤ) :
    (hypercubicLattice 2).Walk ![x0, y] ![x1, y] :=
  if h : x0 ≤ x1 then
    (sw_horizR y x0 (x1 - x0).toNat).copy rfl
      (by rw [Int.toNat_of_nonneg (by linarith)]; norm_num)
  else
    ((sw_horizR y x1 (x0 - x1).toNat).reverse).copy
      (by rw [Int.toNat_of_nonneg (by linarith)]; norm_num) rfl


noncomputable def sw_vertSeg (x y0 y1 : ℤ) :
    (hypercubicLattice 2).Walk ![x, y0] ![x, y1] :=
  if h : y0 ≤ y1 then
    (sw_vertU x y0 (y1 - y0).toNat).copy rfl
      (by rw [Int.toNat_of_nonneg (by linarith)]; norm_num)
  else
    ((sw_vertU x y1 (y0 - y1).toNat).reverse).copy
      (by rw [Int.toNat_of_nonneg (by linarith)]; norm_num) rfl


end Lattice
end StatMech
