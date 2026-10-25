/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part10
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
open scoped BigOperators


namespace StatMech

namespace Exact3D

noncomputable def classifyFiniteCutoffStableKey {d : ℕ} (K : TailCutoff)
    (c : FiniteCutoffCoordinate d K) :
    BoundedPolymerCase.StableKey K.maxDegree K.maxRange :=
  BoundedPolymerCase.stableKey (classifyFiniteCutoffCoordinate K c)


noncomputable def classifyFiniteCutoffMinimalCubicStableKey {d : ℕ}
    (K : TailCutoff) (c : FiniteCutoffCoordinate d K) :
    BoundedPolymerCase.StableKey K.maxDegree K.maxRange :=
  BoundedPolymerCase.classifyByMinimalCubicStableKey
    (classifyFiniteCutoffCoordinate K c)

end Exact3D
end StatMech
