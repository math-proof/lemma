/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailBoundSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Abbrev.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton
open scoped BigOperators


namespace StatMech

namespace Exact3D

def toBoundedLocalCoordinate {d : ℕ} {K : TailCutoff}
    (c : FiniteCutoffCoordinate d K) :
    BoundedPolymerCase.BoundedLocalCoordinate d K.radius K.maxDegree K.maxRange :=
  ⟨c.1, by simpa [InsideFiniteCutoff] using c.2⟩


noncomputable def classifyFiniteCutoffCoordinate {d : ℕ} (K : TailCutoff)
    (c : FiniteCutoffCoordinate d K) : FiniteCutoffCase d K :=
  BoundedPolymerCase.classifyBoundedLocalCoordinate (toBoundedLocalCoordinate c)


end Exact3D
end StatMech
