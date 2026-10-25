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
universe u


namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

/-- The multiplication-by-`n` endomorphism `[n]` on the group of points of a Weierstrass
curve, packaged as an additive group homomorphism `W.Point →+ W.Point`. -/
def multiplicationByN (W : WeierstrassCurve.Affine F) (n : ℤ) : W.Point →+ W.Point :=
  zsmulAddGroupHom n

/-- The `n`-torsion subgroup `E[n]` of a Weierstrass curve, defined as the kernel of the
multiplication-by-`n` homomorphism. -/
def torsionSubgroup (W : WeierstrassCurve.Affine F) (n : ℤ) : AddSubgroup W.Point :=
  (multiplicationByN W n).ker

end WeierstrassCurve.Affine
