/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFamilyAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part4


namespace StatMech.Universality

open Complex

open scoped BigOperators


variable {V : Type*} [DecidableEq V]


theorem hexBdryAssign_identity {D : HexDomain V} {P : D.InteriorPairing}
    {R : HexRegion} (hsub : P.interior ⊆ D.incidences)
    (A : HexRegionAssign D P R) (hFa : A.Fa = 1) :
    hexBdryCl * A.lam + hexBdryCt * (A.taup + A.taum) + A.ups = 1 := by
  have h := hexBoundary_identity_via_family D P hsub A.toFamilyData (by simpa using hFa)
  simpa using h


theorem hexBdryAssign_identity_scales {D : ℕ → HexDomain V}
    {P : ∀ v, (D v).InteriorPairing} {R : ℕ → HexRegion}
    (hsub : ∀ v, (P v).interior ⊆ (D v).incidences)
    (A : ∀ v, HexRegionAssign (D v) (P v) (R v))
    (hFa : ∀ v, 1 ≤ v → (A v).Fa = 1) :
    ∀ v, 1 ≤ v →
      hexBdryCl * (A v).lam + hexBdryCt * ((A v).taup + (A v).taum) + (A v).ups = 1 := by
  intro v hv
  exact hexBdryAssign_identity (hsub v) (A v) (hFa v hv)


theorem hexCell_mid_zero_re (c : ℂ) :
    ((hexCell c).mid (0 : Fin 1) (0 : Fin 3)).re = Real.sqrt 3 / 4 := by
  show ((1 / 2 : ℂ) * hexUnit (2 * ((0 : Fin 3) : ℤ))).re = Real.sqrt 3 / 4
  have hh : (2 * ((0 : Fin 3) : ℤ)) = (0 : ℤ) := by decide
  rw [hh]
  have e0 : hexUnit (0 : ℤ) = Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) := by
    unfold hexUnit; congr 1; push_cast; ring
  rw [e0, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_six]
  simp; ring


theorem hexCell_mid_two_re (c : ℂ) :
    ((hexCell c).mid (0 : Fin 1) (2 : Fin 3)).re = 0 := by
  show ((1 / 2 : ℂ) * hexUnit (2 * ((2 : Fin 3) : ℤ))).re = 0
  have hh : (2 * ((2 : Fin 3) : ℤ)) = (4 : ℤ) := by decide
  rw [hh]
  have e4 : hexUnit (4 : ℤ) = Complex.exp (((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    unfold hexUnit; congr 1; push_cast; ring
  rw [e4, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring,
      Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp


theorem hexRegionCls_hexCell_two (c : ℂ) (R : HexRegion)
    (hne : (hexCell c).mid (0 : Fin 1) (2 : Fin 3) ≠ R.start) :
    hexRegionCls R ((hexCell c).mid (0 : Fin 1) (2 : Fin 3)) = 1 :=
  hexRegionCls_left R (hexCell_mid_two_re c) hne

end StatMech.Universality
