/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part9


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decNontrivialRootedEquivNonemptyFactors
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    {w : {w : List (ons_Dart L) //
        ons_validRootedList d (ons_dartRev L d) w} //
      2 ≤ w.1.length} ≃
    {segments : {segments : List (List (ons_Dart L)) //
        ons_validFactorList d (ons_dartRev L d) segments} //
      segments.1 ≠ []} :=
  Equiv.subtypeEquiv
    (ons_rootedFactorEquiv d (ons_dartRev L d)
      (ons_dartRev_ne L d).symm)
    (fun w ↦ ons_rootedList_nontrivial_iff_factors_ne_nil
      d (ons_dartRev L d) w.1 w.2)

noncomputable def ons_decNonemptyAtomsEquivNonemptyFactors
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    {atoms : List (ons_DecFirstReturnAtom L d) // atoms ≠ []} ≃
    {segments : {segments : List (List (ons_Dart L)) //
        ons_validFactorList d (ons_dartRev L d) segments} //
      segments.1 ≠ []} :=
  Equiv.subtypeEquiv
    (ons_decFirstReturnAtomsEquivFactorList L d)
    (fun atoms ↦ by
      rw [ons_decFirstReturnAtomsEquivFactorList_apply_val]
      unfold ons_decFirstReturnAtomsSegments
      simp)


noncomputable def ons_decRootedAtomEquivNonemptyAtoms
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    ons_DecRootedAtom L d ≃
      {atoms : List (ons_DecFirstReturnAtom L d) // atoms ≠ []} :=
  (ons_decRootedAtomEquivRootedList L d).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (ons_validRootedList d (ons_dartRev L d))
      (fun w ↦ 2 ≤ w.length)).symm |>.trans <|
    (ons_decNontrivialRootedEquivNonemptyFactors L d).trans
      (ons_decNonemptyAtomsEquivNonemptyFactors L d).symm

end StatMech.Onsager
