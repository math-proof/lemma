/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part7
import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopClassification.Part2


namespace StatMech.Onsager

open Finset SimpleGraph

noncomputable def ons_decSquarefreeLoopFinset
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L)) :
    Finset (Fin n → ons_Dart L) :=
  Finset.univ.filter fun d ↦
    ons_decLoopExponent L d = ons_finsetExponent S ∧
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) d ≠ 0

end StatMech.Onsager
