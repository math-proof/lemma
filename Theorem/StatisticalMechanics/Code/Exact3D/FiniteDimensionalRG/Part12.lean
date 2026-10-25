/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Def.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part13


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplittingExample

theorem splitting_cone_iterate {η : ℝ} (hη : 0 ≤ η)
    {x : FiniteHyperbolicSplitting.State 1} (hx : splitting.cone η x)
    (k : ℕ) :
    splitting.cone η (splitting.iterate k x) :=
  splitting.cone_iterate hη hx k


end FiniteHyperbolicSplittingExample
end Exact3D
end StatMech
