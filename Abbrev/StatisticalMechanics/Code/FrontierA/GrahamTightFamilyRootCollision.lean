/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyRootCollision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


abbrev CanonicalTightOpposingRootCuts
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) : Prop :=
  ∃ a b : leftMaskFiber ends m j k l zero p,
      CanonicalTransferWorks ends m k zero a.1.1 c.1.1 ∧
      CanonicalTransferWorks ends m k zero b.1.1 d.1.1 ∧
      canonicalTranslatedRow ends m k zero a.1.1 c.1.1 =
        canonicalTranslatedRow ends m k zero b.1.1 d.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero b.1.1 c.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero a.1.1 d.1.1 ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero b.1.1 c.1.1 ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero a.1.1 d.1.1


abbrev CanonicalTightTwoRowCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) : Prop :=
  ∃ q1 q2 : rightMaskFiber ends m j k l zero p,
      q1 ≠ q2 ∧
      q1 ∈ canonicalMaskRightImages ends m j k l zero p c ∧
      q1 ∈ canonicalMaskRightImages ends m j k l zero p d ∧
      q2 ∈ canonicalMaskRightImages ends m j k l zero p c ∧
      q2 ∈ canonicalMaskRightImages ends m j k l zero p d


abbrev CanonicalTightRootCollisionDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) : Prop :=
  CanonicalTightOpposingRootCuts ends m j k l zero p c d ∨
    CanonicalTightTwoRowCollision ends m j k l zero p c d

end StatMech.GrahamGHS.FourColor
