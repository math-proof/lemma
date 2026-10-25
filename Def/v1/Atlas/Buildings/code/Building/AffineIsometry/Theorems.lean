/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometry/Theorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.AffineIsometry.LatticeChains
import Structure.v1.Atlas.Buildings.code.Building.AffineIsometry.Theorems
set_option linter.unusedSectionVars false

open AffineIsometryBuilding DVRContext


namespace AnisotropicFormContext

variable (ctx : AnisotropicFormContext)

/-- The maximal lattice of an anisotropic form: the $\mathfrak{o}$-lattice
$\{v : \langle v, v \rangle \in \mathfrak{o}\}$ of vectors with integral
self-pairing. -/
def maxLat : OLattice ctx.C where
  carrier := {v | ctx.C.isInO (ctx.form v v)}
  zero_mem := ctx.form_zero_isInO
  add_mem := fun hx hy => ctx.selfpair_add_closed _ _ hx hy
  smul_mem := by
    intro r x hx
    show ctx.C.isInO (ctx.form (ctx.C.oscal r x) (ctx.C.oscal r x))

    have oscal_eq : ctx.C.oscal r x = ctx.C.embed r • x := by
      ext i; simp [DVRContext.oscal, Pi.smul_apply, smul_eq_mul]
    rw [oscal_eq, ctx.form_smul_left, ctx.form_smul_right]

    exact ctx.isInO_mul (ctx.isInO_embed r) (ctx.isInO_mul (ctx.isInO_embed r) hx)
  spans_V := ctx.spans_data
  closed_under_o_combination := by
    intro coeffs vectors hcoeffs hvecs
    exact ctx.closed_under_o_combination_data coeffs vectors hcoeffs
      (fun i => hvecs i)

end AnisotropicFormContext
