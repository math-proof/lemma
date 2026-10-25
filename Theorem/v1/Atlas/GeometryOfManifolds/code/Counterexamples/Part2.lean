/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Instance.v1.Atlas.GeometryOfManifolds.code.Counterexamples
set_option autoImplicit false

open DifferentialFormSpace


namespace KTGamma

/-- Unfold the `Group` multiplication on `KTGamma` to `mul'`. -/
@[simp] lemma mul_def (g h : KTGamma) : g * h = mul' g h := rfl

/-- Unfold the identity of `KTGamma` to `one'`. -/
@[simp] lemma one_def : (1 : KTGamma) = one' := rfl

/-- Unfold the inverse of `KTGamma` to `inv'`. -/
@[simp] lemma inv_def (g : KTGamma) : g⁻¹ = inv' g := rfl

end KTGamma
