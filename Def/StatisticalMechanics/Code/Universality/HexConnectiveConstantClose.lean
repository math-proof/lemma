/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRealizeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexZDivTauClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHammersleyWelshClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexConnectiveConstantClose


namespace StatMech.Universality

open Filter Topology

open scoped Topology Real NNReal BigOperators


noncomputable def hxf_wc : ℕ → ℝ := fun n => (hexChiE⁻¹) ^ n


end StatMech.Universality
