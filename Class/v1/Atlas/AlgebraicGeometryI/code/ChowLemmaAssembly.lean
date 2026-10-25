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
open AlgebraicGeometry CategoryTheory Limits

universe u


noncomputable section

namespace ChowLemma

/-- A scheme is proper (as an abstract property) when it is equipped with a proper morphism to
some base scheme `S`. -/
class IsProper (X : Scheme.{u}) : Prop where
  exists_proper_morphism : ∃ (S : Scheme.{u}) (f : X ⟶ S), AlgebraicGeometry.IsProper f

end ChowLemma
end
