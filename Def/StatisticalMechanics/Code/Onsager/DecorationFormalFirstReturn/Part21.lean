/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part19


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decBoundedRootEquivUnbounded
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    {root : ons_DecRootedAtomBounded L d (ons_finsuppTotalDegree m) //
      ons_decBoundedRootExponent root = m} ≃
    {root : ons_DecRootedAtom L d //
      ons_decRootedAtomExponent root = m} :=
  Equiv.ofBijective (ons_decBoundedRootToUnbounded L d m)
    (ons_decBoundedRootToUnbounded_bijective L d m)

noncomputable def ons_decBoundedRootEquivBoundedTuples
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hk : 0 < m s(d, ons_dartRev L d)) :
    {root : ons_DecRootedAtomBounded L d (ons_finsuppTotalDegree m) //
      ons_decBoundedRootExponent root = m} ≃
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m) //
      (∑ i, ons_decBoundedAtomExponent (atoms i)) = m} :=
  (ons_decBoundedRootEquivUnbounded L d m).trans
    (ons_decRootedExponentEquivBoundedTuples L d m hk)

end StatMech.Onsager
