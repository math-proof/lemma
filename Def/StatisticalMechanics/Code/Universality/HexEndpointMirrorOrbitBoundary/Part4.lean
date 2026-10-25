/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthBoundaryWinding.Part4
import Structure.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part2


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


variable (Kc : DCSClassification H)

noncomputable def pairClassMass (k : HexPairedBoundaryClass) : ℝ :=
  ∑ i : I, if Kc.classOf i = k then 2 * (H.pairs i).mass else 0

noncomputable def fixedMass : ℝ := ∑ k : K, (H.fixed k).mass


noncomputable def dcsLam : ℝ := H.pairClassMass Kc .side

noncomputable def dcsTau : ℝ := H.pairClassMass Kc .slant

noncomputable def dcsUps : ℝ := H.pairClassMass Kc .top + H.fixedMass

end HexEndpointMirrorOrbitData
end
end StatMech.Universality
