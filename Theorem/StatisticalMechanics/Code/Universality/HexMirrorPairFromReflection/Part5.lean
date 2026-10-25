/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairedBoundaryNormalized
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part4


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


namespace HexFiniteStripReflectedPairing

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexFiniteStripBoundaryCore R h0 D P}


theorem classMass_nonneg
    (S : HexFiniteStripReflectedPairing (ι := ι) C)
    (A : DCSAngles S) (k : HexPairedBoundaryClass) :
    0 ≤ HexFiniteStripMirrorPairedData.classMass S.toMirrorPairedData
      (A.toClassification S) k := by
  classical
  unfold HexFiniteStripMirrorPairedData.classMass
    HexFiniteStripMirrorPairedData.classMassTerm
  apply Finset.sum_nonneg
  intro i _
  split
  · exact mul_nonneg (by norm_num) (S.pair_mass_nonneg i)
  · exact le_rfl


theorem classMass_pos_of_pair
    (S : HexFiniteStripReflectedPairing (ι := ι) C)
    (A : DCSAngles S) (k : HexPairedBoundaryClass) (i : ι)
    (hik : A.classOf i = k) (hi : 0 < (S.pair i).mass) :
    0 < HexFiniteStripMirrorPairedData.classMass S.toMirrorPairedData
      (A.toClassification S) k := by
  classical
  unfold HexFiniteStripMirrorPairedData.classMass
  apply Finset.sum_pos'
    (fun j _ => by
      unfold HexFiniteStripMirrorPairedData.classMassTerm
      split
      · exact mul_nonneg (by norm_num) (S.pair_mass_nonneg j)
      · exact le_rfl)
  refine ⟨i, Finset.mem_univ i, ?_⟩
  change 0 < if A.classOf i = k then 2 * (S.pair i).mass else 0
  rw [if_pos hik]
  positivity


theorem normalized_class_value_pos_of_pair
    (S : HexFiniteStripReflectedPairing (ι := ι) C)
    (A : DCSAngles S) (k : HexPairedBoundaryClass) (i : ι)
    (hik : A.classOf i = k) (hi : 0 < (S.pair i).mass) :
    0 < hexChi⁻¹ *
      HexFiniteStripMirrorPairedData.classMass S.toMirrorPairedData
        (A.toClassification S) k :=
  mul_pos (inv_pos.mpr hexChi_pos) (S.classMass_pos_of_pair A k i hik hi)


theorem normalized_class_values_nonneg
    (S : HexFiniteStripReflectedPairing (ι := ι) C)
    (A : DCSAngles S) :
    0 ≤ HexFiniteStripMirrorPairedData.dcsLam S.toMirrorPairedData
        (A.toClassification S) ∧
      0 ≤ HexFiniteStripMirrorPairedData.dcsTau S.toMirrorPairedData
        (A.toClassification S) ∧
      0 ≤ HexFiniteStripMirrorPairedData.dcsUps S.toMirrorPairedData
        (A.toClassification S) := by
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hexChi_pos.le)
      (S.classMass_nonneg A .side)
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hexChi_pos.le)
      (S.classMass_nonneg A .slant)
  · exact mul_nonneg (inv_nonneg.mpr hexChi_pos.le)
      (S.classMass_nonneg A .top)


theorem normalized_dcs_identity
    (S : HexFiniteStripReflectedPairing (ι := ι) C)
    (A : DCSAngles S) :
    hexCl * HexFiniteStripMirrorPairedData.dcsLam S.toMirrorPairedData
        (A.toClassification S)
      + hexCt * HexFiniteStripMirrorPairedData.dcsTau S.toMirrorPairedData
        (A.toClassification S)
      + HexFiniteStripMirrorPairedData.dcsUps S.toMirrorPairedData
        (A.toClassification S) = 1 :=
  HexFiniteStripMirrorPairedData.normalized_dcs_identity
    S.toMirrorPairedData (A.toClassification S)

end HexFiniteStripReflectedPairing
end StatMech.Universality
