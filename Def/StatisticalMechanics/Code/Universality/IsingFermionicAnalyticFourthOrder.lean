/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility.Part3
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Group.Bounded


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
