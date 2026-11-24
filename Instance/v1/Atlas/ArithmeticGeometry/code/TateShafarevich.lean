module
public import Mathlib
public import Def.v1.Atlas.ArithmeticGeometry.code.WeilChatelet.Part2
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.WeilChatelet
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisCohomology
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.WCGroupH1
public import Abbrev.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part3
public import Def.v1.Atlas.ArithmeticGeometry.code.WCGroupH1
public import Abbrev.v1.Atlas.ArithmeticGeometry.code.TateShafarevich


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TateShafarevich.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

universe u

open NumberField GaloisCohomology

/-- The transported additive commutative group structure on the Weil-Châtelet group, coming from
its bijection with the first Galois cohomology group $H^1$. -/
noncomputable instance instAddCommGroupWeilChateletGroup {k : Type u} [Field k]
    (E : EllipticCurveOver k) : AddCommGroup (WeilChateletGroup E) :=
  haveI := E.isElliptic
  WC.addCommGroupOfData (WCH1Data.mk' k E.curve (ECurvePointsAlgClosure k E.curve)
    (AbsGaloisGroup k))

end
