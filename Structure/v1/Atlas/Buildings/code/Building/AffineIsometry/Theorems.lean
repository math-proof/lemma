/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometry/Theorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.AffineIsometry.LatticeChains
set_option linter.unusedSectionVars false

open AffineIsometryBuilding DVRContext


/-- An anisotropic symmetric bilinear form context: a symmetric bilinear form
$\langle \cdot, \cdot \rangle$ over $k$ that is anisotropic (no nonzero
isotropic vectors), together with the ambient DVR data, Hensel-style
solvability of quadratic equations, and closure properties of the integral
self-pairings. Used to construct the maximal lattice on which the form is
integral. -/
structure AnisotropicFormContext where
  C : DVRContext
  form : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k
  form_symm : ∀ v w : Fin C.n → C.k, form v w = form w v
  form_add_left : ∀ v₁ v₂ w : Fin C.n → C.k,
    form (v₁ + v₂) w = form v₁ w + form v₂ w
  form_smul_left : ∀ (c : C.k) (v w : Fin C.n → C.k),
    form (c • v) w = c * form v w
  anisotropic : ∀ v : Fin C.n → C.k, form v v = 0 → v = 0
  two_is_unit : C.isUnitInO (C.embed (1 + 1 : C.𝔬))
  hensel : ∀ (b c : C.k),
    C.isUnitInO b → C.isInMaxIdeal c →
    ∃ α : C.k, α * α + b * α + c = 0


  isInO_zero : C.isInO (0 : C.k)
  isInO_add : ∀ {x y : C.k}, C.isInO x → C.isInO y → C.isInO (x + y)
  isInO_mul : ∀ {x y : C.k}, C.isInO x → C.isInO y → C.isInO (x * y)
  isInO_neg : ∀ {x : C.k}, C.isInO x → C.isInO (-x)
  isUnitInO_inv : ∀ {x : C.k}, C.isUnitInO x → C.isInO x⁻¹
  isInO_embed : ∀ r : C.𝔬, C.isInO (C.embed r)


  selfpair_add_closed : ∀ v w : Fin C.n → C.k,
    C.isInO (form v v) → C.isInO (form w w) → C.isInO (form (v + w) (v + w))


  spans_data : ∀ v : Fin C.n → C.k,
    ∃ (m : ℕ) (cs : Fin m → C.k) (vs : Fin m → Fin C.n → C.k),
      (∀ j, C.isInO (form (vs j) (vs j))) ∧ v = ∑ j, cs j • vs j

