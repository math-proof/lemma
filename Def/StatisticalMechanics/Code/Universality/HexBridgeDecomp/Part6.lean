/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part5


namespace StatMech.Universality

open List


def bridgeDecomp : (γ : List (ℕ × ℤ)) → hexHW_WF γ → List HexBridge
  | [], _ => []
  | p :: rest, h =>
    let hwpos : 0 < p.1 := h p List.mem_cons_self
    (⟨p.1, hwpos, (hexHW_leadRun p rest).map Prod.snd, hexHW_leadRun_content_ne p rest⟩ :
        HexBridge)
      :: bridgeDecomp (hexHW_dropRun p rest) (hexHW_WF_dropRun p rest h)
  termination_by γ _ => γ.length
  decreasing_by exact hexHW_dropRun_length_lt p rest

end StatMech.Universality
