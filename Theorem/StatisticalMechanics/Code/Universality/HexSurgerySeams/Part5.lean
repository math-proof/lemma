module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
public import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
public import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
public import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
public import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
public import Def.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex HexWalk List Filter

open scoped Topology BigOperators


theorem hexZ_conv_seams_closed (c : ℕ → ℝ) (x : ℝ) (hx : 0 < x)
    (hlt : x < hexChiE) (hc : ∀ n, 0 ≤ c n)
    (C : ∀ T, HexColumn T hexChiE)
    (H : ∀ N, HexHWDataRecon c (fun T => (C T).colSum x) x N) :
    Summable (fun n => c n * x ^ n) :=
  hexZ_conv_recon_from_geometry c x hx hlt hc C H

end StatMech.Universality
