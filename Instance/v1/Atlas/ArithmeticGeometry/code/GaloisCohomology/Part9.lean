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
import Def.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part8
open groupCohomology


section PrincipalCrossedHom

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- Promote the Galois `DistribMulAction` on $E(\bar k)$ to an `instance`. -/
noncomputable instance instDistribMulActionGaloisOnECurvePoints (k : Type*) [Field k]
    (W : WeierstrassCurve k) :
    DistribMulAction (AbsGaloisGroup k) (ECurvePointsAlgClosure k W) :=
  galoisDistribMulAction k W

/-- We endow $E(\bar k)$ with the discrete topology, which is appropriate for the topology on
the cocycle group. -/
noncomputable instance instTopologicalSpaceECurvePointsAlgClosure (k : Type*) [Field k]
    (W : WeierstrassCurve k) :
    TopologicalSpace (ECurvePointsAlgClosure k W) := ⊥

/-- Confirmation that the topology on $E(\bar k)$ chosen above is the discrete topology. -/
instance instDiscreteTopologyECurvePointsAlgClosure (k : Type*) [Field k]
    (W : WeierstrassCurve k) :
    DiscreteTopology (ECurvePointsAlgClosure k W) := ⟨rfl⟩

/-- Addition on $E(\bar k)$ is continuous (vacuously, since the topology is discrete). -/
instance instContinuousAddECurvePointsAlgClosure (k : Type*) [Field k]
    (W : WeierstrassCurve k) :
    ContinuousAdd (ECurvePointsAlgClosure k W) where
  continuous_add := continuous_of_discreteTopology

/-- Negation on $E(\bar k)$ is continuous (vacuously, in the discrete topology). -/
instance instContinuousNegECurvePointsAlgClosure (k : Type*) [Field k]
    (W : WeierstrassCurve k) :
    ContinuousNeg (ECurvePointsAlgClosure k W) where
  continuous_neg := continuous_of_discreteTopology

end PrincipalCrossedHom
