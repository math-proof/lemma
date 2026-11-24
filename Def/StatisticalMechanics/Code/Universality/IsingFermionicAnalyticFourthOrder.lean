module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility.Part3
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Group.Bounded


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open InnerProductSpace

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def complexLineCLM (d : Complex) :
    Real →L[Real] Complex :=
  Complex.ofRealCLM.smulRight d


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
