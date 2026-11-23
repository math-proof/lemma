/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/TwoDimDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
public import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
public import Def.v1.Atlas.GeometryOfManifolds.code.TwoDimDFS
@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000


noncomputable section

/-- Each degree of polynomial forms on $\mathbb{R}^2$ inherits an additive commutative group. -/
noncomputable instance symp2AddCommGroup : ∀ p, AddCommGroup (Symp2Ω p)
  | 0 => inferInstanceAs (AddCommGroup Poly2)
  | 1 => inferInstanceAs (AddCommGroup (Poly2 × Poly2))
  | 2 => inferInstanceAs (AddCommGroup Poly2)
  | _ + 3 => inferInstanceAs (AddCommGroup PUnit)

/-- Each degree of polynomial forms on $\mathbb{R}^2$ inherits an $\mathbb{R}$-module structure. -/
noncomputable instance symp2Module : ∀ p, Module ℝ (Symp2Ω p)
  | 0 => inferInstanceAs (Module ℝ Poly2)
  | 1 => inferInstanceAs (Module ℝ (Poly2 × Poly2))
  | 2 => inferInstanceAs (Module ℝ Poly2)
  | _ + 3 => inferInstanceAs (Module ℝ PUnit)


end
