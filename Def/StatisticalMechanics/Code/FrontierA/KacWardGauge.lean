/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardTheta
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
open scoped BigOperators


namespace StatMech.FrontierA

open Matrix


noncomputable def kwGaugeConjugate
    {D : Type*} [Fintype D] [DecidableEq D]
    (gauge : D -> ℂ) (M : Matrix D D ℂ) : Matrix D D ℂ :=
  fun i j => (gauge i)⁻¹ * M i j * gauge j


end StatMech.FrontierA
