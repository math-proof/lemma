/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part16


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decBoundedTupleToUnbounded
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m) //
      (∑ i, ons_decBoundedAtomExponent (atoms i)) = m} →
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtom L d //
      (∑ i, ons_decFirstReturnAtomExponent (atoms i)) = m} :=
  fun atoms ↦ ⟨fun i ↦ ons_decForgetBoundedAtom (atoms.1 i), by
    simpa using atoms.2⟩

end StatMech.Onsager
