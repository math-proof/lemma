/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part15


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decFirstReturnAtom_externalExponent
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atom : ons_DecFirstReturnAtom L d) :
    ons_decFirstReturnAtomExponent atom s(d, ons_dartRev L d) = 1 :=
  ons_decLoopExponent_external_eq_one_of_firstReturn
    L d atom.2.1 atom.2.2

theorem ons_decFirstReturnAtoms_externalExponent_sum
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atoms : List (ons_DecFirstReturnAtom L d)) :
    (atoms.map ons_decFirstReturnAtomExponent).sum
        s(d, ons_dartRev L d) = atoms.length := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      simp only [List.map_cons, List.sum_cons, Finsupp.add_apply,
        List.length_cons, ih, ons_decFirstReturnAtom_externalExponent]
      omega

end StatMech.Onsager
