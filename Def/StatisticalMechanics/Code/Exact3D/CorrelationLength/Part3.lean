/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Exact3D.CorrelationLength

@[expose] public section

namespace StatMech

namespace Exact3D

noncomputable def PlaceholderModel : CriticalModel Unit where
  betaC := 0
  twoPoint := fun _ _ _ => 0

end Exact3D
end StatMech
