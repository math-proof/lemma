/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/K0GeneratorsOverlay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.K0GeneratorsOverlay


namespace K0Gen

/-- The Grothendieck group `K^0(Coh X)`: free abelian group on coherent sheaves modulo
short-exact-sequence relations. -/
abbrev K0Coh (X : SmoothCurveK0Data) : Type :=
  FreeAbelianGroup X.CohSheaf ⧸ sesRelations X

end K0Gen
