/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.LinearAlgebra.Lagrange
import Instance.v1.Atlas.ArithmeticGeometry.code.CompleteVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CompleteVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveComplete
import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
import Structure.v1.Atlas.ArithmeticGeometry.code.ProjectiveComplete
import Def.v1.Atlas.ArithmeticGeometry.code.EllipticCurves
universe u


class IsAlgebraicGroup (k : outParam (Type u)) [Field k] (V : Type u) [TopologicalSpace V] [Group V] : Prop where
  toIsTopologicalGroup : IsTopologicalGroup V
  isVariety :
    ∃ (algV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (hcarrier : algV.carrier = V),
      (hcarrier ▸ algV.topInst = ‹TopologicalSpace V›)
  mul_isMorphism :
    ∃ (algV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (algVV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (hV : algV.carrier = V) (hVV : algVV.carrier = (V × V))
      (f : algVV.carrier → algV.carrier),

      (∀ p : algVV.carrier, cast hV (f p) =
        (cast hVV p).1 * (cast hVV p).2) ∧

      AlgebraicGeometry.CompletenessValuationCriterion.IsMorphismOfVarieties algVV algV f
  inv_isMorphism :
    ∃ (algV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (hV : algV.carrier = V)
      (f : algV.carrier → algV.carrier),

      (∀ v : algV.carrier, cast hV (f v) = (cast hV v)⁻¹) ∧

      AlgebraicGeometry.CompletenessValuationCriterion.IsMorphismOfVarieties algV algV f


