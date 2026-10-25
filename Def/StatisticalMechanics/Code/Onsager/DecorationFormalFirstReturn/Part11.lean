/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part10


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decFirstReturnAtomExponent
    {L : ℕ} {d : ons_Dart L}
    (atom : ons_DecFirstReturnAtom L d) : ons_DecEdge L →₀ ℕ :=
  ons_decLoopExponent L atom.2.1

noncomputable def ons_decFirstReturnAtomWeight
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) {d : ons_Dart L}
    (atom : ons_DecFirstReturnAtom L d) : ℂ :=
  ons_decLoopScalar L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) atom.2.1

noncomputable def ons_decRootedAtomExponent
    {L : ℕ} {d : ons_Dart L}
    (root : ons_DecRootedAtom L d) : ons_DecEdge L →₀ ℕ :=
  ons_decLoopExponent L root.2.1

noncomputable def ons_decRootedAtomWeight
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) {d : ons_Dart L}
    (root : ons_DecRootedAtom L d) : ℂ :=
  ons_decLoopScalar L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) root.2.1

end StatMech.Onsager
