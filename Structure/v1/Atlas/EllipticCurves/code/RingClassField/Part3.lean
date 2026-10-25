/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.PointCounting.Part2
import Lemma.Complex.Atlas.v1.EllipticCurves.code.PointCounting
import Lemma.Complex.Atlas.v1.EllipticCurves.code.OrdinarySupersingular
import Lemma.Complex.Atlas.v1.EllipticCurves.code.HilbertClassPolynomial
import Lemma.Complex.Atlas.v1.EllipticCurves.code.CMTorsor
import Def.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
import Def.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial.Part2
import Def.v1.Atlas.EllipticCurves.code.CMTorsor.Part7
import Class.v1.Atlas.EllipticCurves.code.RingClassField
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
