/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Topology.Algebra.MulAction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.SeparableClosure
import Instance.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part8
open groupCohomology


section PrincipalCrossedHom

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The Galois group $\mathrm{Gal}(\bar k/k)$ acts on $E(\bar k)$ by transporting points along
each $k$-algebra automorphism of $\bar k$. -/
noncomputable def galoisDistribMulAction (k : Type*) [Field k] (W : WeierstrassCurve k) :
    DistribMulAction (AbsGaloisGroup k) (ECurvePointsAlgClosure k W) where
  smul σ P := WeierstrassCurve.Affine.Point.map σ.toAlgHom P
  one_smul P := by
    show WeierstrassCurve.Affine.Point.map (AlgEquiv.refl.toAlgHom (R := k)) P = P
    cases P with
    | zero => rfl
    | some x y h => simp [WeierstrassCurve.Affine.Point.map_some]
  mul_smul σ τ P := by
    show WeierstrassCurve.Affine.Point.map (σ * τ).toAlgHom P =
      WeierstrassCurve.Affine.Point.map σ.toAlgHom
        (WeierstrassCurve.Affine.Point.map τ.toAlgHom P)
    rw [WeierstrassCurve.Affine.Point.map_map]
    cases P with
    | zero => rfl
    | some x y h => simp [WeierstrassCurve.Affine.Point.map_some]
  smul_zero σ := by
    show WeierstrassCurve.Affine.Point.map σ.toAlgHom 0 = 0
    exact WeierstrassCurve.Affine.Point.map_zero σ.toAlgHom
  smul_add σ P Q := by
    show WeierstrassCurve.Affine.Point.map σ.toAlgHom (P + Q) =
      WeierstrassCurve.Affine.Point.map σ.toAlgHom P +
        WeierstrassCurve.Affine.Point.map σ.toAlgHom Q
    exact (WeierstrassCurve.Affine.Point.map σ.toAlgHom).map_add P Q

end PrincipalCrossedHom
