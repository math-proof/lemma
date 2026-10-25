/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailBoundSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Def.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton
open scoped BigOperators


namespace StatMech

namespace Exact3D

abbrev FiniteCutoffCoordinate (d : ℕ) (K : TailCutoff) : Type :=
  {c : LocalPolymerCoordinate d // InsideFiniteCutoff K c}


abbrev TailCoordinate (d : ℕ) (K : TailCutoff) : Type :=
  {c : LocalPolymerCoordinate d // OutsideFiniteCutoff K c}


abbrev FiniteCutoffCase (d : ℕ) (K : TailCutoff) : Type :=
  BoundedPolymerCase d K.radius K.maxDegree K.maxRange


abbrev FiniteCutoffTable (d : ℕ) (K : TailCutoff) : Type :=
  RatInterval.CaseTable (FiniteCutoffCase d K)


end Exact3D
end StatMech
