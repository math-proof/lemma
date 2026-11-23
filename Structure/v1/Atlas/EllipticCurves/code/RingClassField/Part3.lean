/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.EllipticCurves.code.PointCounting.Part2
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.PointCounting
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.OrdinarySupersingular
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.HilbertClassPolynomial
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.CMTorsor
public import Def.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
public import Def.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial.Part2
public import Def.v1.Atlas.EllipticCurves.code.CMTorsor.Part7
public import Class.v1.Atlas.EllipticCurves.code.RingClassField
public section

open NumberField

open Elliptic_Curves


namespace CMMethod

/-- Predicate saying that the elliptic curve `E/F` has prescribed
`j`-invariant `j₀ ∈ F`. -/
structure CMOutput (F : Type*) [Field F] [Fintype F] [DecidableEq F] where
  curve : WeierstrassCurve.Affine F
  trace : ℤ
  frob_trace_eq : Hasse.traceFrobenius curve = trace ∨
                  Hasse.traceFrobenius curve = -trace

end CMMethod
