/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/BoundedHeightFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Heights.Part4
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Heights
open TateTheorem CanonicalHeight Filter


noncomputable section

attribute [local instance] Classical.dec

variable {K : Type*} [Field K] [NumberField K]

variable (W : WeierstrassCurve K) [W.IsElliptic]

end
