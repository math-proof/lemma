/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.StatisticalMechanics.Code.Exact3D.CorrelationLength.Part3


public section

namespace StatMech

namespace Exact3D

structure BlockScale where
  L : ℕ
  one_lt : 1 < L

end Exact3D
end StatMech
