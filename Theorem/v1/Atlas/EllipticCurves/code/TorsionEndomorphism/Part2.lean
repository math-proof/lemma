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
import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part2
universe u


namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

/-- Membership characterisation: a point `P ∈ E(K)` lies in `E(K)[n]` iff `n • P = 0`. -/
@[simp]
lemma EllipticCurve.mem_torsionSubgroup
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K]
    (n : ℤ) (P : (E.map (algebraMap k K)).toProjective.Point) :
    P ∈ EllipticCurve.torsionSubgroup k E K n ↔ n • P = 0 := by
  simp [EllipticCurve.torsionSubgroup]

end WeierstrassCurve.Affine
