/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightRootCutHallEquivalence
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part5
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskRightEdgeDegreeDominance_of_selectedOppositeClosure
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (hclose : CanonicalMaskRightSelectedOppositeClosure
      ends m j k l zero p) :
    CanonicalMaskRightEdgeDegreeDominance ends m j k l zero p :=
  canonicalMaskRightEdgeDegreeDominance_of_preimageEmbedding
    ends m j k l zero p
      (canonicalMaskRightEdgePreimageEmbedding_of_selectedOppositeClosure
        ends m j k l zero hloop hjk hkl p hclose)

end StatMech.GrahamGHS.FourColor
