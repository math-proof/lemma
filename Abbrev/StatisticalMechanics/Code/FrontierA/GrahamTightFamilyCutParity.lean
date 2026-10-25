/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyCutParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyRootCollision
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


abbrev CanonicalOpposingRootCutsAtRight
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (q : rightMaskFiber ends m j k l zero p) : Prop :=
  ∃ a b : leftMaskFiber ends m j k l zero p,
    CanonicalTransferWorks ends m k zero a.1.1 c.1.1 ∧
    CanonicalTransferWorks ends m k zero b.1.1 d.1.1 ∧
    q.1.1 = balancedSwap m
      (canonicalMiddleTransfer ends m a.1.1 k zero)
      (canonicalOuterTransfer ends m a.1.1 k zero) c.1.1 ∧
    q.1.1 = balancedSwap m
      (canonicalMiddleTransfer ends m b.1.1 k zero)
      (canonicalOuterTransfer ends m b.1.1 k zero) d.1.1 ∧
    ¬ CanonicalTransferWorks ends m k zero b.1.1 c.1.1 ∧
    ¬ CanonicalTransferWorks ends m k zero a.1.1 d.1.1 ∧
    CanonicalTranslatedRowRootComponentCut
      ends m k zero b.1.1 c.1.1 ∧
    CanonicalTranslatedRowRootComponentCut
      ends m k zero a.1.1 d.1.1

end StatMech.GrahamGHS.FourColor
