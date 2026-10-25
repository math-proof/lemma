/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyRootCollision
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
import Def.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalCollisionOppositeRow_consecutive_symmDiff
    (m : Finset I) (q r c d e : ↑m -> Fin 4) :
    canonicalCollisionOppositeRow m q c d ∆
        canonicalCollisionOppositeRow m r d e =
      rowClass m q 0 ∆ rowClass m r 0 ∆
        rowClass m c 0 ∆ rowClass m e 0 := by
  unfold canonicalCollisionOppositeRow
  calc
    (rowClass m q 0 ∆ rowClass m c 0 ∆ rowClass m d 0) ∆
          (rowClass m r 0 ∆ rowClass m d 0 ∆ rowClass m e 0) =
        (rowClass m d 0 ∆ rowClass m d 0) ∆
          (rowClass m q 0 ∆ rowClass m r 0 ∆
            rowClass m c 0 ∆ rowClass m e 0) := by ac_rfl
    _ = _ := by simp


theorem sources_consecutive_canonicalCollisionOppositeRows
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (q r : rightMaskFiber ends m j k l zero p)
    (c d e : leftMaskFiber ends m j k l zero p) :
    StatMech.Sharpness.RandomCurrent.sources ends
        (canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1 ∆
          canonicalCollisionOppositeRow m r.1.1 d.1.1 e.1.1) = ∅ := by
  rw [canonicalCollisionOppositeRow_consecutive_symmDiff,
    StatMech.Sharpness.RandomCurrent.sources_symmDiff,
    StatMech.Sharpness.RandomCurrent.sources_symmDiff,
    StatMech.Sharpness.RandomCurrent.sources_symmDiff]
  rw [(rightPattern_rowBoundaries q.1.2).1,
    (rightPattern_rowBoundaries r.1.2).1,
    (leftPattern_rowBoundaries c.1.2).1,
    (leftPattern_rowBoundaries e.1.2).1]
  simp


end StatMech.GrahamGHS.FourColor
