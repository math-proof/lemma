module
public import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRoch
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRoch
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardProjective
public import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part7
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.AdjoinRoot
public import Instance.v1.Atlas.AlgebraicGeometryI.code.ConicRational.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ConicRational.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace ConicRational

section ProjectiveConic

variable (k : Type*) [CommRing k]

/-- The defining polynomial of the projective conic `X·Y = Z²` in `P^2`. -/
noncomputable def conicPoly : MvPolynomial (Fin 3) k :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.X 2 ^ 2

end ProjectiveConic


section GenusRationality

/-- The genus-degree formula for a smooth plane curve of degree `d`: `g = (d-1)(d-2)/2`. -/
def genusDeg (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2

end GenusRationality
end ConicRational
