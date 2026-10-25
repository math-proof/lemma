/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripBoundary.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBoundConcrete.Part4
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripNormalization


namespace StatMech.Universality

open Complex HexWalk


theorem hexVBC_normalized_start_eq_one (a : ℂ) (h0 : ℤ) :
    normalizedParafObservable (hexVBCRegion a h0).inRegion a h0 a (5 / 8) hexChi = 1 := by
  rw [normalizedParafObservable, hexVBC_start_observable_eq_hexChi]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hexChi_pos))

variable {V : Type*} [DecidableEq V]


theorem hexVBC_boundaryData_Fa_eq_hexChi (a : ℂ) (h0 : ℤ)
    (D : HexDomain V) (P : D.InteriorPairing)
    (B : HexFiniteStripBoundaryData (hexVBCRegion a h0) h0 D P) :
    B.Fa = hexChi := by
  apply Complex.ofReal_injective
  calc
    (B.Fa : ℂ) = D.obs (hexVBCRegion a h0).start := B.Fa_eq
    _ = parafObservable (hexVBCRegion a h0).inRegion
          (hexVBCRegion a h0).start h0 (hexVBCRegion a h0).start (5 / 8) hexChi :=
        B.obs_eq _
    _ = (hexChi : ℂ) := hexVBC_start_observable_eq_hexChi a h0


theorem hexVBC_boundaryData_Fa_ne_one (a : ℂ) (h0 : ℤ)
    (D : HexDomain V) (P : D.InteriorPairing)
    (B : HexFiniteStripBoundaryData (hexVBCRegion a h0) h0 D P) :
    B.Fa ≠ 1 := by
  rw [hexVBC_boundaryData_Fa_eq_hexChi a h0 D P B]
  exact hexChi_ne_one

end StatMech.Universality
