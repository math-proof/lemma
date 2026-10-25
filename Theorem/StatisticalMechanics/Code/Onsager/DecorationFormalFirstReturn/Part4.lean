/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part4


namespace StatMech.Onsager

open BigOperators Finset

@[simp] theorem ons_decFirstReturnAtomEquivSegment_apply_val
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atom : ons_DecFirstReturnAtom L d) :
    (ons_decFirstReturnAtomEquivSegment L d atom).1 =
      ons_decFirstReturnAtomSegment atom := rfl

theorem ons_decFirstReturnAtom_exponent_segment
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atom : ons_DecFirstReturnAtom L d) :
    ons_pathSum (ons_decTransitionExponent L)
        (ons_decFirstReturnAtomSegment atom) =
      ons_decLoopExponent L atom.2.1 := by
  exact ons_decFirstReturnSegment_pathSum_eq_loopExponent
    L d atom.2.1 atom.2.2.1

theorem ons_decFirstReturnAtom_weight_segment
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (atom : ons_DecFirstReturnAtom L d) :
    ons_edgeWeight
        (ons_KWmatWeightedPhase L (fun _ ↦ 1) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        (ons_decFirstReturnAtomSegment atom) =
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) atom.2.1 := by
  exact ons_decFirstReturnSegment_edgeWeight_eq_loopScalar
    L a b d atom.2.1 atom.2.2.1

end StatMech.Onsager
