/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part17


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decBoundedTupleEquivUnbounded
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m) //
      (∑ i, ons_decBoundedAtomExponent (atoms i)) = m} ≃
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtom L d //
      (∑ i, ons_decFirstReturnAtomExponent (atoms i)) = m} :=
  Equiv.ofBijective (ons_decBoundedTupleToUnbounded L d m)
    (ons_decBoundedTupleToUnbounded_bijective L d m)

noncomputable def ons_decRootedExponentEquivBoundedTuples
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hk : 0 < m s(d, ons_dartRev L d)) :
    {root : ons_DecRootedAtom L d //
      ons_decRootedAtomExponent root = m} ≃
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m) //
      (∑ i, ons_decBoundedAtomExponent (atoms i)) = m} :=
  (ons_decRootedExponentEquivUnboundedTuples L d m hk).trans
    (ons_decBoundedTupleEquivUnbounded L d m).symm

end StatMech.Onsager
