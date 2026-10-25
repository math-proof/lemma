/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part16


namespace StatMech.Onsager

open BigOperators Finset

@[simp] theorem ons_decForgetBoundedAtom_exponent
    {L N : ℕ} {d : ons_Dart L}
    (atom : ons_DecFirstReturnAtomBounded L d N) :
    ons_decFirstReturnAtomExponent (ons_decForgetBoundedAtom atom) =
      ons_decBoundedAtomExponent atom := rfl

@[simp] theorem ons_decForgetBoundedAtom_weight
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) {N : ℕ} {d : ons_Dart L}
    (atom : ons_DecFirstReturnAtomBounded L d N) :
    ons_decFirstReturnAtomWeight L a b (ons_decForgetBoundedAtom atom) =
      ons_decBoundedAtomWeight L a b atom := rfl

end StatMech.Onsager
