/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailRG
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG.Part2


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockRGPackage

variable {n : ℕ} {α : Type}


@[simp] theorem with_larger_c_blockBounds
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|) :
    (P.with_larger_c hc hc_lt_one hdominated).blockBounds =
      P.blockBounds :=
  rfl

@[simp] theorem with_larger_c_c
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|) :
    (P.with_larger_c hc hc_lt_one hdominated).c = c' :=
  rfl

@[simp] theorem with_larger_c_thermal
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|) :
    (P.with_larger_c hc hc_lt_one hdominated).thermal = P.thermal :=
  rfl


end FinitePlusTailBlockRGPackage
end Exact3D
end StatMech
