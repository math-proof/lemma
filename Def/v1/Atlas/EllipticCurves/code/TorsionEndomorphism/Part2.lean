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
import Theorem.v1.Atlas.EllipticCurves.code.TorsionEndomorphism
universe u


namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

/-- A Weierstrass curve `W` over a field of characteristic `p` is ordinary if its
`p`-torsion `E[p]` is isomorphic to `ℤ/pℤ` (cf. Definition 6.2 of Sutherland). -/
def IsOrdinary (W : WeierstrassCurve.Affine F) (p : ℕ) [CharP F p] [Fact (Nat.Prime p)] :
    Prop :=
  Nonempty ((torsionSubgroup W (p : ℤ)) ≃+ ZMod p)

/-- A Weierstrass curve `W` over a field of characteristic `p` is supersingular if its
`p`-torsion `E[p]` is trivial (cf. Definition 6.2 of Sutherland). -/
def IsSupersingular (W : WeierstrassCurve.Affine F) (p : ℕ) [CharP F p]
    [Fact (Nat.Prime p)] : Prop :=
  torsionSubgroup W (p : ℤ) = ⊥

/-- The `n`-torsion subgroup `E(K)[n]` of an elliptic curve `E/k` after base change to a
field extension `K`, defined as the torsion subgroup of the projective point group. -/
def EllipticCurve.torsionSubgroup
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K]
    (n : ℤ) : AddSubgroup (E.map (algebraMap k K)).toProjective.Point :=
  AddSubgroup.torsionBy (E.map (algebraMap k K)).toProjective.Point n

end WeierstrassCurve.Affine
