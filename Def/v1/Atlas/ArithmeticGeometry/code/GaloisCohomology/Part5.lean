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
import Theorem.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part5
open groupCohomology


section PrincipalCrossedHom

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The principal crossed hom $\sigma \mapsto \sigma \cdot P - P$ associated to a point $P \in A$. -/
def principalCrossedHom (P : A) : CrossedHom G A where
  toFun σ := σ • P - P
  cocycle_condition :=
    IsPrincipalCrossedHom.isCrossedHom ⟨P, fun _ => rfl⟩

/-- The subgroup of principal crossed homomorphisms (1-coboundaries) inside the additive group of
all crossed homomorphisms. -/
def principalCrossedHomSubgroup (G A : Type*) [Group G] [AddCommGroup A]
    [DistribMulAction G A] : AddSubgroup (CrossedHom G A) where
  carrier := { α | IsPrincipalCrossedHom (α : G → A) }
  zero_mem' := ⟨0, fun σ => by simp [smul_zero]⟩
  add_mem' := by
    rintro α β ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P + Q, fun σ => by
      simp only [CrossedHom.add_apply, smul_add]
      rw [← hP, ← hQ]
      abel⟩
  neg_mem' := by
    rintro α ⟨P, hP⟩
    exact ⟨-P, fun σ => by
      simp only [CrossedHom.neg_apply, smul_neg]
      rw [← hP]
      abel⟩

/-- The principal continuous crossed hom $\sigma \mapsto \sigma \cdot P - P$ associated to
$P \in A$, viewed as a `ContCrossedHom`. -/
def contPrincipalCrossedHom (P : A) : ContCrossedHom G A where
  toCrossedHom := principalCrossedHom P
  continuous_toFun := by
    show Continuous (fun σ => σ • P - P)
    simp only [sub_eq_add_neg]
    exact (continuous_id.smul continuous_const).add continuous_const.neg

/-- The subgroup of continuous principal crossed homomorphisms inside `ContCrossedHom G A`. -/
def contPrincipalCrossedHomSubgroup (G A : Type*) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [TopologicalSpace G] [TopologicalSpace A]
    [ContinuousAdd A] [ContinuousNeg A] [ContinuousSMul G A] :
    AddSubgroup (ContCrossedHom G A) where
  carrier := { α | IsPrincipalCrossedHom (α : G → A) }
  zero_mem' := ⟨0, fun σ => by simp [smul_zero]⟩
  add_mem' := by
    rintro α β ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P + Q, fun σ => by
      simp only [ContCrossedHom.add_apply, smul_add]
      rw [← hP, ← hQ]
      abel⟩
  neg_mem' := by
    rintro α ⟨P, hP⟩
    exact ⟨-P, fun σ => by
      simp only [ContCrossedHom.neg_apply, smul_neg]
      rw [← hP]
      abel⟩

end PrincipalCrossedHom
