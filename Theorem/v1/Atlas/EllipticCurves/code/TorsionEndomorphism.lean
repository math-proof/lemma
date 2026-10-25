/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism
universe u


namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

/-- Any additive group homomorphism between point groups of Weierstrass curves preserves
the `n`-torsion subgroup. -/
theorem map_mem_torsionSubgroup {W₁ W₂ : WeierstrassCurve.Affine F}
    (φ : W₁.Point →+ W₂.Point) (n : ℤ) (P : W₁.Point)
    (hP : P ∈ torsionSubgroup W₁ n) :
    φ P ∈ torsionSubgroup W₂ n := by
  simp only [mem_torsionSubgroup] at hP ⊢
  rw [← φ.map_zsmul, hP, map_zero]

end WeierstrassCurve.Affine
