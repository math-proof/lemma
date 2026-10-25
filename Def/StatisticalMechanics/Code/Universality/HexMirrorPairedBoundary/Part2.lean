/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexGenuineStripPhaseObstruction
import Structure.StatisticalMechanics.Code.Universality.HexMirrorPairedBoundary.Part2


namespace StatMech.Universality

open Complex Set

open scoped BigOperators


namespace HexFiniteStripMirrorPairedData

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexFiniteStripBoundaryCore R h0 D P}


noncomputable def pairedContribution
    (H : HexFiniteStripMirrorPairedData (ι := ι) C) : ℝ :=
  ∑ i : ι, 2 * Real.cos (H.pairs i).angle * (H.pairs i).mass


end HexFiniteStripMirrorPairedData
end StatMech.Universality
