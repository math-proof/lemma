/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing
open SimpleGraph


namespace StatMech.BeffaraDC

open StatMech.Onsager


@[simp] theorem torusHorizontalEdge_val (L : ℕ) [Fact (2 < L)]
    (x y : ZMod L) :
    (torusHorizontalEdge L x y : Sym2 (ZMod L × ZMod L)) =
      s((x, y), (x + 1, y)) := rfl

@[simp] theorem torusVerticalEdge_val (L : ℕ) [Fact (2 < L)]
    (x y : ZMod L) :
    (torusVerticalEdge L x y : Sym2 (ZMod L × ZMod L)) =
      s((x, y), (x, y + 1)) := rfl


theorem torusHorizontalEdge_orientation_independent
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusHorizontalEdge L x y : Sym2 (ZMod L × ZMod L)) =
      s((x + 1, y), (x, y)) := by
  rw [torusHorizontalEdge_val, Sym2.eq_swap]


theorem torusVerticalEdge_orientation_independent
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusVerticalEdge L x y : Sym2 (ZMod L × ZMod L)) =
      s((x, y + 1), (x, y)) := by
  rw [torusVerticalEdge_val, Sym2.eq_swap]


end StatMech.BeffaraDC
