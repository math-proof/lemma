module
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.Isogenies
public import Theorem.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u


namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

/-- Definition 6.13: the endomorphism ring `End(E) = Hom(E, E)` as the additive monoid of
endomorphisms of `E.Point`, with multiplication given by composition. -/
abbrev EndRing : Type u :=
  AddMonoid.End E.Point

end WeierstrassCurve.Affine
