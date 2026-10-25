/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyRootCollision
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part4
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalCoverageNormalizedBoundaryRow
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (d : ↑m -> Fin 4) (rho : Fin 2) : Prop :=
  StatMech.Sharpness.RandomCurrent.connK
      ends (rowClass m d rho) k zero ∧
    StatMech.Sharpness.RandomCurrent.sources
        ends (edgeComponent ends (rowClass m d rho) zero) =
      (if rho = 0 then ({j, k} : Finset W) else ({k, l} : Finset W)) ∧
    StatMech.Sharpness.RandomCurrent.sources ends
        (rowClass m d rho \ edgeComponent ends (rowClass m d rho) zero) = ∅ ∧
    Disjoint (canonicalTransferUnion ends m k zero d)
      (rowClass m d rho \ edgeComponent ends (rowClass m d rho) zero)


end StatMech.GrahamGHS.FourColor
