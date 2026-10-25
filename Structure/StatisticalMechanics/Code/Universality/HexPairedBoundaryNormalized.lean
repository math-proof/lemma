/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairedBoundaryNormalized.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairedBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Inductive.StatisticalMechanics.Code.Universality.HexPairedBoundaryNormalized


namespace StatMech.Universality

open scoped BigOperators


namespace HexFiniteStripMirrorPairedData

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexFiniteStripBoundaryCore R h0 D P}


structure DCSClassification
    (H : HexFiniteStripMirrorPairedData (ι := ι) C) where
  classOf : ι → HexPairedBoundaryClass
  cos_angle : ∀ i,
    Real.cos (H.pairs i).angle =
      match classOf i with
      | .side => hexCl
      | .slant => hexCt
      | .top => 1

end HexFiniteStripMirrorPairedData
end StatMech.Universality
