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
import Theorem.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part2
universe u


namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

/-- Definition 6.13: the endomorphism ring `End(E) = Hom(E, E)` as the additive monoid of
endomorphisms of `E.Point`, with multiplication given by composition. -/
abbrev EndRing : Type u :=
  AddMonoid.End E.Point

end WeierstrassCurve.Affine
