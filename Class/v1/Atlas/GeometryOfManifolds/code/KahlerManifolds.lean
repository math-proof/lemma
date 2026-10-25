/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/KahlerManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part4
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AlmostComplexManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ArnoldConjecture
import Class.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture.Part4
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
set_option autoImplicit false


noncomputable section

open scoped Manifold


section DFSKahler

open DifferentialFormSpace


/-- A function $\varphi$ is strictly plurisubharmonic when the $(1,1)$-form $\partial\bar\partial\varphi$ is nondegenerate as a pairing on vector fields. -/
class IsStrictlyPlurisubharmonic
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst)) (φ : Ω 0) : Prop where
  nondeg : Function.Injective (fun (X : VF) => inst.ι X (dol.del (dol.delbar φ)))


end DFSKahler
end
