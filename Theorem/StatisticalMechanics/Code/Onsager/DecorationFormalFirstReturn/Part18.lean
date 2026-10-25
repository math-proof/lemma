/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part19


namespace StatMech.Onsager

open BigOperators Finset

@[simp] theorem ons_decForgetBoundedRoot_exponent
    {L N : ℕ} {d : ons_Dart L}
    (root : ons_DecRootedAtomBounded L d N) :
    ons_decRootedAtomExponent (ons_decForgetBoundedRoot root) =
      ons_decBoundedRootExponent root := rfl

@[simp] theorem ons_decForgetBoundedRoot_weight
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) {N : ℕ} {d : ons_Dart L}
    (root : ons_DecRootedAtomBounded L d N) :
    ons_decRootedAtomWeight L a b (ons_decForgetBoundedRoot root) =
      ons_decBoundedRootWeight L a b root := rfl

end StatMech.Onsager
