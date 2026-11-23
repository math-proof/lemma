/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/BoundedHeightFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.ArithmeticGeometry.code.Heights.Part4
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Heights
open TateTheorem CanonicalHeight Filter

public section

noncomputable section

attribute [local instance] Classical.dec

variable {K : Type*} [Field K] [NumberField K]

variable (W : WeierstrassCurve K) [W.IsElliptic]

end
