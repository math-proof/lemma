/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Abbrev.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part3


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decBoundedAtomExponent
    {L N : ℕ} {d : ons_Dart L}
    (atom : ons_DecFirstReturnAtomBounded L d N) :
    ons_DecEdge L →₀ ℕ :=
  ons_decLoopExponent L atom.2.1

noncomputable def ons_decBoundedAtomWeight
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) {d : ons_Dart L} {N : ℕ}
    (atom : ons_DecFirstReturnAtomBounded L d N) : ℂ :=
  ons_decLoopScalar L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) atom.2.1

end StatMech.Onsager
