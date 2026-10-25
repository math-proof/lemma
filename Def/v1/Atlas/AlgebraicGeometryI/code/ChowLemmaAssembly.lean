/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowLemmaAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.AlgebraicGeometryI.code.ChowLemmaHelper
import Def.v1.Atlas.AlgebraicGeometryI.code.ChowHelperBlowupProjective
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ChowHelperBlowupProjective
import Class.v1.Atlas.AlgebraicGeometryI.code.ChowLemmaAssembly
open AlgebraicGeometry CategoryTheory Limits

universe u


noncomputable section

namespace ChowLemma

/-- A scheme is projective when it embeds as a closed subscheme of some `Proj 𝒜`. -/
def IsProjective (X : Scheme.{u}) : Prop :=
  ChowHelperBlowupProjective.IsProjectiveScheme X

/-- Two schemes are birational when they share a common dense open subscheme. -/
def Birational (X Y : Scheme.{u}) : Prop :=
  ChowHelperBlowupProjective.IsBirational X Y

end ChowLemma
end
