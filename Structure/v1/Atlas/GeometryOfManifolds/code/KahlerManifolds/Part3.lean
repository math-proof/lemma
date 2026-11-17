/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/KahlerManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part4
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.AlmostComplexManifolds
public import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ArnoldConjecture
public import Class.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture.Part4
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Class.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds
set_option autoImplicit false


public noncomputable section

open scoped Manifold


section DFSKahler

open DifferentialFormSpace


/-- A $(0,1)$-form represented by real and imaginary $1$-forms $(\mathrm{re}, \mathrm{im})$ satisfying the type condition $\iota_X \mathrm{im} = \iota_{JX} \mathrm{re}$. -/
structure Form01
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst)) where
  re : Ω 1
  im : Ω 1
  type_cond : ∀ (X : VF), inst.ι X im = inst.ι (J.J X) re

end DFSKahler
end
