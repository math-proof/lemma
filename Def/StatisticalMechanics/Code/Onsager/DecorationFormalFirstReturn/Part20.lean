/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part18


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decBoundedRootToUnbounded
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    {root : ons_DecRootedAtomBounded L d (ons_finsuppTotalDegree m) //
      ons_decBoundedRootExponent root = m} →
    {root : ons_DecRootedAtom L d //
      ons_decRootedAtomExponent root = m} :=
  fun root ↦ ⟨ons_decForgetBoundedRoot root.1, by simpa using root.2⟩

end StatMech.Onsager
