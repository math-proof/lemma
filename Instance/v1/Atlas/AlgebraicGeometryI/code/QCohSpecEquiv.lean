/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohSpecEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Def.v1.Atlas.AlgebraicGeometryI.code.QCohSpecEquiv

@[expose] public section

open AlgebraicGeometry CategoryTheory


noncomputable section

universe u

variable {R : CommRingCat.{u}}

/-- The unit of the `tilde ⊣ Γ` adjunction is an isomorphism (the affine
reconstruction `Γ(M̃) ≅ M`). -/
instance tilde_unit_isIso : IsIso (tilde.adjunction (R := R)).unit :=
  tilde.adjunction.isIso_unit_of_iso (tilde.toTildeΓNatIso (R := R)).symm

end
