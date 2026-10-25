/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part2


namespace StatMech.Onsager

open BigOperators Finset

abbrev ons_DecFirstReturnAtom
    (L : ℕ) (d : ons_Dart L) :=
  Σ n : ℕ, {loop : Fin (n + 1) → ons_Dart L //
    ons_decIsFirstReturnLoop d loop}

end StatMech.Onsager
