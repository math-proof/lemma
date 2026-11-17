/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.AlgebraicGeometryI.code.SmoothnessOmega
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SmoothnessOmega

public section

noncomputable section

open KaehlerDifferential Algebra IsLocalRing

universe u v

section Prop30Characterization

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

end Prop30Characterization
end
