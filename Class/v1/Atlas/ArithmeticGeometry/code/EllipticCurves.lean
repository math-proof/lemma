module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.GroupTheory.Torsion
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.LinearAlgebra.Lagrange
public import Instance.v1.Atlas.ArithmeticGeometry.code.CompleteVarieties
public import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
public import Structure.v1.Atlas.ArithmeticGeometry.code.ProjectiveComplete
public section
universe u

class IsProjectiveVariety (k : outParam (Type u)) [Field k] (V : Type u) [TopologicalSpace V] :
    Prop where
  exists_algVariety_projective :
    ∃ (_ : IsAlgClosed k)
      (algV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (hcarrier : algV.carrier = V),
      (hcarrier ▸ algV.topInst = ‹TopologicalSpace V›) ∧
      Nonempty (AlgebraicGeometry.CompletenessValuationCriterion.IsProjectiveVariety algV)

