/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/K0GeneratorsOverlay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Def.v1.Atlas.AlgebraicGeometryI.code.K0GeneratorsOverlay

@[expose] public section


namespace K0Gen

/-- The Grothendieck group `K^0(Coh X)`: free abelian group on coherent sheaves modulo
short-exact-sequence relations. -/
abbrev K0Coh (X : SmoothCurveK0Data) : Type :=
  FreeAbelianGroup X.CohSheaf ⧸ sesRelations X

end K0Gen
