/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthBoundaryWinding.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

namespace HexEndpointMirrorOrbitData

variable {I K V : Type*} [Fintype I] [Fintype K]

variable [DecidableEq I] [DecidableEq K] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexEndpointBoundaryCore R h0 D P}

variable (H : HexEndpointMirrorOrbitData (I := I) (K := K) C)


structure DCSClassification where
  classOf : I → HexPairedBoundaryClass
  cos_angle : ∀ i,
    Real.cos (H.pairs i).angle =
      match classOf i with
      | .side => hexCl
      | .slant => hexCt
      | .top => 1

end HexEndpointMirrorOrbitData
end
end StatMech.Universality
