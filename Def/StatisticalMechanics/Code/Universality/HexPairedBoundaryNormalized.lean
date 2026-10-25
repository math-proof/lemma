/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairedBoundaryNormalized.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairedBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Structure.StatisticalMechanics.Code.Universality.HexPairedBoundaryNormalized


namespace StatMech.Universality

open scoped BigOperators


namespace HexFiniteStripMirrorPairedData

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexFiniteStripBoundaryCore R h0 D P}


variable (H : HexFiniteStripMirrorPairedData (ι := ι) C)

variable (K : DCSClassification H)


noncomputable def classMassTerm (k : HexPairedBoundaryClass) (i : ι) : ℝ :=
  if K.classOf i = k then 2 * (H.pairs i).mass else 0


noncomputable def classMass (k : HexPairedBoundaryClass) : ℝ :=
  ∑ i : ι, classMassTerm H K k i


noncomputable def dcsLam : ℝ := hexChi⁻¹ * classMass H K .side


noncomputable def dcsTau : ℝ := hexChi⁻¹ * classMass H K .slant


noncomputable def dcsUps : ℝ := hexChi⁻¹ * classMass H K .top

end HexFiniteStripMirrorPairedData
end StatMech.Universality
