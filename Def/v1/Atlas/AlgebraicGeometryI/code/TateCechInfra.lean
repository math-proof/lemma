module
public import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityTate.Part3
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityTate
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityAnnihilator
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.SerreDualityAnnihilator


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
section TateVectorSpaceDef

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Two subspaces `W₁`, `W₂` of `V` are commensurable iff their quotients by
their intersection are both finite-dimensional. -/
def IsCommensurable (W₁ W₂ : Submodule k V) : Prop :=
  Module.Finite k (W₁ ⧸ Submodule.comap W₁.subtype (W₁ ⊓ W₂)) ∧
  Module.Finite k (W₂ ⧸ Submodule.comap W₂.subtype (W₁ ⊓ W₂))

end TateVectorSpaceDef
