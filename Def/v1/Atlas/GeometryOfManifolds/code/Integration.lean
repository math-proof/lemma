/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Integration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.HodgeTheory
public import Structure.v1.Atlas.GeometryOfManifolds.code.Integration

@[expose] public section

set_option autoImplicit false

open DifferentialFormSpace


namespace StokesIntegration

variable {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]

/-- The $L^2$ inner product on $p$-forms induced by the Hodge-star pairing:
$\langle \alpha, \beta \rangle = \int \alpha \wedge \star \beta$. -/
def inner_prod (S : StokesIntegration (inst := inst)) (p : ℕ) (α β : Ω p) : ℝ :=
  S.integrate (S.wedge_star p α β)

end StokesIntegration
