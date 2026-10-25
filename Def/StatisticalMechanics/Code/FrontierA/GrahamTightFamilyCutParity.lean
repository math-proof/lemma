/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyRootCollision
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalRowSupportRootComponentCut
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (K : Finset I) : Prop :=
  (StatMech.Sharpness.RandomCurrent.connK ends K k zero ∧
      edgeComponent ends K zero = edgeComponent ends K k) ∨
    (StatMech.Sharpness.RandomCurrent.connK ends (m \ K) k zero ∧
      edgeComponent ends (m \ K) zero = edgeComponent ends (m \ K) k)


def canonicalCollisionOppositeRow
    (m : Finset I) (q c d : ↑m -> Fin 4) : Finset I :=
  rowClass m q 0 ∆ rowClass m c 0 ∆ rowClass m d 0


end StatMech.GrahamGHS.FourColor
