/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
public import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
public import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
public import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part10
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

public inductive SourceClassCardinalityCase where
  | zero
  | two
  | fourPlus
deriving DecidableEq, Fintype

end Exact3D
end StatMech
