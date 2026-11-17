/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointAnalyticAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointInputAssembly.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicAnalyticFourthOrder
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalFourthOrder.Part2


namespace StatMech.Universality

open Filter Topology

public noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure LocalDiagonalFourthOrderAnalyticData
    (Phi : Complex -> Complex) (z : Complex) (h boundOne boundTwo : Real) :
    Prop where
  one : CenteredFourthOrderSegmentData
    (fun t : Real =>
      (Phi (z + (t : Complex) * (1 + Complex.I))).im) h boundOne
  two : CenteredFourthOrderSegmentData
    (fun t : Real =>
      (Phi (z + (t : Complex) * (1 - Complex.I))).im) h boundTwo
  analytic : AnalyticAt Complex Phi z


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
