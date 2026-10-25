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
import Instance.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part9
open groupCohomology


section PrincipalCrossedHom

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The Galois action on $E(\bar k)$ is continuous (in the Krull topology on $\mathrm{Gal}(\bar k/k)$
and the discrete topology on $E(\bar k)$): the stabilizer of every point is open, since it
contains the open subgroup fixing a finite subextension containing the coordinates of $P$. -/
noncomputable def galoisContinuousSMul (k : Type*) [Field k] (W : WeierstrassCurve k) :
    @ContinuousSMul (AbsGaloisGroup k) (ECurvePointsAlgClosure k W)
      (galoisDistribMulAction k W).toSMul
      (absGaloisGroupTopologicalSpace k)
      (instTopologicalSpaceECurvePointsAlgClosure k W) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro P
  suffices h : ∃ (E : IntermediateField k (AlgebraicClosure k)),
      FiniteDimensional k E ∧ E.fixingSubgroup ≤ MulAction.stabilizer _ P by
    obtain ⟨E, _, hle⟩ := h
    exact Subgroup.isOpen_of_mem_nhds
      (MulAction.stabilizer (AbsGaloisGroup k) P)
      (Filter.mem_of_superset
        ((IntermediateField.fixingSubgroup_isOpen E).mem_nhds E.fixingSubgroup.one_mem)
        hle)
  change ECurvePointsAlgClosure k W at P
  match P with
  | .zero =>
    exact ⟨⊥, IntermediateField.instFiniteSubtypeMemBot k, fun σ _ => by
      simp only [MulAction.mem_stabilizer_iff]
      show WeierstrassCurve.Affine.Point.map σ.toAlgHom .zero = .zero
      exact WeierstrassCurve.Affine.Point.map_zero σ.toAlgHom⟩
  | .some x y h =>
    refine ⟨IntermediateField.adjoin k {x, y},
      IntermediateField.finiteDimensional_adjoin (fun z _ =>
        isAlgebraic_iff_isIntegral.mp ((AlgebraicClosure.isAlgebraic k).isAlgebraic z)),
      fun σ hσ => ?_⟩
    simp only [MulAction.mem_stabilizer_iff]
    show WeierstrassCurve.Affine.Point.map σ.toAlgHom (.some x y h) = .some x y h
    have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ
    have hx : σ x = x :=
      hσ' x (IntermediateField.subset_adjoin k _ (Set.mem_insert x {y}))
    have hy : σ y = y :=
      hσ' y (IntermediateField.subset_adjoin k _ (Set.mem_insert_iff.mpr (Or.inr rfl)))
    simp only [WeierstrassCurve.Affine.Point.map_some, AlgEquiv.toAlgHom_eq_coe,
      AlgHom.coe_coe, hx, hy]

end PrincipalCrossedHom
