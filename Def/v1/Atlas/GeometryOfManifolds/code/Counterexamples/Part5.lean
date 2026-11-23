/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
public import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
public import Instance.v1.Atlas.GeometryOfManifolds.code.Counterexamples.Part2

@[expose] public section

set_option autoImplicit false

open DifferentialFormSpace


/-- The free rank of the abelianization $\Gamma^{\mathrm{ab}}$ of the Kodaira–Thurston group. -/
def KTGamma.abelianizationFreeRank : ℕ :=
  FreeAbelianRank.rank (G := Multiplicative ℤ × Multiplicative ℤ × Multiplicative ℤ)


