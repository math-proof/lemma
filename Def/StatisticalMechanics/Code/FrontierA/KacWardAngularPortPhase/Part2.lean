/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortEmbedding.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortPhase.Part2


namespace StatMech.FrontierA

open SimpleGraph

noncomputable def kwRawDirectionRoot (a : ℝ) : ℂ :=
  Complex.exp (((a : ℂ) * Complex.I) / 2)

end StatMech.FrontierA
