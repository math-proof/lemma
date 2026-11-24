module
public import Mathlib
public import Def.v1.Atlas.ArithmeticGeometry.code.WeilChatelet.Part2
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.WeilChatelet
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisCohomology
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.WCGroupH1
public import Abbrev.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part3
public import Def.v1.Atlas.ArithmeticGeometry.code.WCGroupH1
public import Abbrev.v1.Atlas.ArithmeticGeometry.code.TateShafarevich.Part2


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

/-- The Galois cohomology group inherits its additive commutative group structure from the
underlying $H^1$ construction. -/
instance GaloisCohomologyH1.instAddCommGroup (k : Type u) [Field k]
    (E : EllipticCurveOver k) : AddCommGroup (GaloisCohomologyH1 k E) :=
  inferInstance

end
