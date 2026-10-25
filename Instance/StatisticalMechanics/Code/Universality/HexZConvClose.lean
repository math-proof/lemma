/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Def.StatisticalMechanics.Code.Universality.HexZConvClose.Part4


namespace StatMech.Universality

open scoped BigOperators

open HexWalk


noncomputable instance hzc_Dn_fintype (a : ℂ) (h0 : ℤ) (N : ℕ) :
    Fintype (hzc_Dn a h0 N) := by
  unfold hzc_Dn; infer_instance


end StatMech.Universality
