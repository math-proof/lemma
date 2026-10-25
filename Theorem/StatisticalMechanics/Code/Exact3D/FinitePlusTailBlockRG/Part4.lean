/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailRG
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG.Part4


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockRGPackage

variable {n : ℕ} {α : Type}


@[simp] theorem hyperbolicSplitting_thermal
    (P : FinitePlusTailBlockRGPackage n α) :
    P.hyperbolicSplitting.thermal = P.thermal :=
  rfl


@[simp] theorem hyperbolicSplitting_stable
    (P : FinitePlusTailBlockRGPackage n α) :
    P.hyperbolicSplitting.stable = P.stableCertificate :=
  rfl


@[simp] theorem with_larger_c_hyperbolicSplitting_stable_map
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|) :
    (P.with_larger_c hc hc_lt_one hdominated).hyperbolicSplitting.stable.map =
      P.hyperbolicSplitting.stable.map :=
  rfl


@[simp] theorem with_larger_constants_hyperbolicSplitting_stable_map
    (P : FinitePlusTailBlockRGPackage n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
    (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
    (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
    (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
    (htt : P.blockBounds.tailToTail ≤ tailToTail')
    (hc_nonneg : 0 ≤ c') (hc_lt_one : c' < 1)
    (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
    (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
    (hdominated : c' ≤ |P.thermal|) :
    (let Q :=
      P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le hdominated;
      Q.hyperbolicSplitting.stable.map = P.hyperbolicSplitting.stable.map) := by
  dsimp


theorem cone_iterate
    (P : FinitePlusTailBlockRGPackage n α)
    {η : ℝ} (hη : 0 ≤ η)
    {x : FinitePlusTailHyperbolicSplitting.State n α}
    (hx : P.hyperbolicSplitting.cone η x) (k : ℕ) :
    P.hyperbolicSplitting.cone η
      (P.hyperbolicSplitting.iterate k x) :=
  P.hyperbolicSplitting.cone_iterate hη hx k


end FinitePlusTailBlockRGPackage
end Exact3D
end StatMech
