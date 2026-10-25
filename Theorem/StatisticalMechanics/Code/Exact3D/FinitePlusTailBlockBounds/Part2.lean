/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part2


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockBounds

variable {n : ℕ} {α : Type*}


@[simp] theorem with_larger_constants_finiteMap
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    (B.with_larger_constants hff htf hft htt).finiteMap = B.finiteMap :=
  rfl

@[simp] theorem with_larger_constants_tailMap
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    (B.with_larger_constants hff htf hft htt).tailMap = B.tailMap :=
  rfl

@[simp] theorem with_larger_constants_map
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    (B.with_larger_constants hff htf hft htt).map = B.map :=
  rfl

@[simp] theorem with_larger_constants_finiteToFinite
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    (B.with_larger_constants hff htf hft htt).finiteToFinite =
      finiteToFinite' :=
  rfl

@[simp] theorem with_larger_constants_tailToFinite
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    (B.with_larger_constants hff htf hft htt).tailToFinite =
      tailToFinite' :=
  rfl

@[simp] theorem with_larger_constants_finiteToTail
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    (B.with_larger_constants hff htf hft htt).finiteToTail =
      finiteToTail' :=
  rfl

@[simp] theorem with_larger_constants_tailToTail
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    (B.with_larger_constants hff htf hft htt).tailToTail =
      tailToTail' :=
  rfl


end FinitePlusTailBlockBounds
end Exact3D
end StatMech
