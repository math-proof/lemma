/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part4


namespace StatMech.Onsager

open Finset SimpleGraph

noncomputable def ons_decWalkOfKWChain
    (L : ℕ) (start : ons_Dart L) :
    (tail : List (ons_Dart L)) →
    List.IsChain (ons_decGeometricStep L) (start :: tail) →
    (ons_decGraph L).Walk start (ons_decKWChainLast start tail)
  | [], _ => .nil
  | target :: rest, hchain => by
      have hstep : target.1 = ons_dirStep L start.2 start.1 :=
        hchain.rel
      let first := ons_decTransitionWalk L target start hstep
      let remaining :=
        ons_decWalkOfKWChain L target rest hchain.tail
      exact first.append remaining

end StatMech.Onsager
