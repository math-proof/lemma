module
public import Def.v1.Atlas.AlgebraicGeometryI.code.TateCechInfra.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.TateCechInfra


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityUnconditional.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace SerreDualityUnconditional

open TateCechInfra SerreDualityCurves

open CanonicalSheafCurves RiemannRochCurves

variable {k : Type*} [Field k]

end SerreDualityUnconditional
end
