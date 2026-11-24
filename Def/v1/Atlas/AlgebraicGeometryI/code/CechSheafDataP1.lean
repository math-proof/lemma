module
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.CechCohomologyIdentification
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CechCohomologyIdentification
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.GenusConstruction
public import Def.v1.Atlas.AlgebraicGeometryI.code.GenusConstruction.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

universe v

namespace CechSheafDataP1

open SerreDualityTate CanonicalSheafCurves GenusConstruction

open TateCechInfra

variable (k : Type) [Field k]


/-- The Tate duality setup for `P¹` with its standard two-open cover: the ambient `k`-vector
space is `k` itself with both subspaces equal to the top subspace. -/
def tateSetupP1 : TateDualitySetup k where
  V := k
  V₁ := ⊤
  V₂ := ⊤

end CechSheafDataP1
end
