/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexInfraReach.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexW3Link


namespace StatMech.Universality

open HexWalk List Filter Topology

open scoped BigOperators Topology Real NNReal


noncomputable def hexW3_dispBridgeDecomp (h0 : ℤ) (γ : List (ℕ × ℤ)) (h : hexHW_WF γ)
    (hPos : ∀ b ∈ bridgeDecomp γ h, 0 < ⌊hexInfra_disp h0 b.content⌋₊) :
    List HexBridge :=
  (bridgeDecomp γ h).attach.map (fun b => hexW3_anchor h0 b.1 (hPos b.1 b.2))


end StatMech.Universality
