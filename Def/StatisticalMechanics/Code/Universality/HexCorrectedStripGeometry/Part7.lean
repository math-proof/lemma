module
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part6


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

def hexCSReflectIncidence {T L : ℕ} (e : HexCSIncidence T L) :
    HexCSIncidence T L :=
  ⟨hexCSReflectVertex e.vtx, hexAWReflectEdge e.edge⟩

end
end StatMech.Universality
