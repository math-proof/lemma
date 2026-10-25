/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexCSInStrip (T L : ℕ) (c : HexAWCoord) : Prop :=
  0 ≤ hexAWBookRe2 c ∧ hexAWBookRe2 c ≤ 3 * T ∧
    c.i ≤ L ∧ c.j ≤ L

end
end StatMech.Universality
