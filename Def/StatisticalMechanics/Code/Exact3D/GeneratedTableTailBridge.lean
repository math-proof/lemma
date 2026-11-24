module
public import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyTailBridge.Part2
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

noncomputable def classifyFiniteCutoffCubicClass {d : ℕ} (K : TailCutoff)
    (c : FiniteCutoffCoordinate d K) :
    CubicClass d K.radius K.maxDegree K.maxRange :=
  cubicClass (classifyFiniteCutoffCoordinate K c)


end BoundedPolymerCase
end Exact3D
end StatMech
