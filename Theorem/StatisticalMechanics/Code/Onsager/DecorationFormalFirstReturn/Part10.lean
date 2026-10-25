/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part10


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decRootedAtomEquivNonemptyAtoms_segments
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (root : ons_DecRootedAtom L d) :
    ons_decFirstReturnAtomsSegments d
        (ons_decRootedAtomEquivNonemptyAtoms L d root).1 =
      ons_firstReturnFactors d (ons_decRootedAtomList root) := by
  let rooted :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (ons_validRootedList d (ons_dartRev L d))
      (fun w ↦ 2 ≤ w.length)).symm
      (ons_decRootedAtomEquivRootedList L d root)
  let factors := ons_decNontrivialRootedEquivNonemptyFactors L d rooted
  let atoms :=
    (ons_decNonemptyAtomsEquivNonemptyFactors L d).symm factors
  have hatoms := congrArg (fun z ↦ z.1.1)
    ((ons_decNonemptyAtomsEquivNonemptyFactors L d).apply_symm_apply factors)
  change ons_decFirstReturnAtomsSegments d atoms.1 = factors.1.1 at hatoms
  change ons_decFirstReturnAtomsSegments d atoms.1 =
    ons_firstReturnFactors d (ons_decRootedAtomList root)
  exact hatoms

end StatMech.Onsager
