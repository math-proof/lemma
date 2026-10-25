/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyTailBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificateExample.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyTailBridgeExample

noncomputable def zeroSplit {d : ℕ} (K : TailCutoff) :
    ContributionSplit (FiniteCutoffCoordinate d K) where
  finiteContribution := fun _ => 0
  tailContribution := fun _ => 0
  totalContribution := fun _ => 0


end StableKeyTailBridgeExample
end BoundedPolymerCase
end Exact3D
end StatMech
