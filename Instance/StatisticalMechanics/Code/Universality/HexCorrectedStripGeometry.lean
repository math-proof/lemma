module
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
public import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex HexWalk

noncomputable section

instance hexCSInStrip_decidable (T L : ℕ) (c : HexAWCoord) :
    Decidable (hexCSInStrip T L c) := by
  unfold hexCSInStrip hexAWBookRe2 hexAWDepth hexAWLong
  infer_instance


end
end StatMech.Universality
