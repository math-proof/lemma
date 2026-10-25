/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorOrbitBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part5
import Structure.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part2


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


namespace HexFiniteStripMirrorOrbitData

variable {I K V : Type*} [Fintype I] [Fintype K]

variable [DecidableEq I] [DecidableEq K] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexFiniteStripBoundaryCore R h0 D P}

variable (H : HexFiniteStripMirrorOrbitData (I := I) (K := K) C)


noncomputable def totalContribution : ℝ :=
  (∑ i : I, 2 * Real.cos (H.pairs i).angle * (H.pairs i).mass) +
    ∑ k : K, (H.fixed k).mass

end HexFiniteStripMirrorOrbitData
end StatMech.Universality
