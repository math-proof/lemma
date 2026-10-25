/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4CorrelationReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4ParameterBridge


namespace StatMech.FrontierD

noncomputable def fkQgt4SixVertexGapRate (q : ℝ) : ℝ :=
  sixVertexAntiferroelectricGapRate
    (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))


def FKQgt4WindingSectorBounds (xiInv R : ℝ) : Prop :=
  R ≤ xiInv ∧
    ∀ r : ℕ, 2 ≤ r → ((r - 1 : ℕ) : ℝ) * xiInv ≤ (r : ℝ) * R


end StatMech.FrontierD
