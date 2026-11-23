/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PolynomialDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
public import Def.v1.Atlas.GeometryOfManifolds.code.PolynomialDFS
@[expose] public section

set_option autoImplicit false


/-- Each degree of polynomial forms inherits an additive commutative group structure. -/
noncomputable instance polyΩ_acg : ∀ p, AddCommGroup (PolyΩ p)
  | 0 => inferInstanceAs (AddCommGroup (Polynomial ℝ))
  | 1 => inferInstanceAs (AddCommGroup (Polynomial ℝ))
  | _ + 2 => inferInstanceAs (AddCommGroup PUnit)

/-- Each degree of polynomial forms inherits an $\mathbb{R}$-module structure. -/
noncomputable instance polyΩ_mod : ∀ p, Module ℝ (PolyΩ p)
  | 0 => inferInstanceAs (Module ℝ (Polynomial ℝ))
  | 1 => inferInstanceAs (Module ℝ (Polynomial ℝ))
  | _ + 2 => inferInstanceAs (Module ℝ PUnit)

