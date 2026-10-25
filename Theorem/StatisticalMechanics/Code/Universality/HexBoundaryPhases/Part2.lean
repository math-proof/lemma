/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexBoundaryPhases.Part2


namespace StatMech.Universality

open Complex

open scoped BigOperators


variable {V : Type*} [DecidableEq V]
  {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}


namespace HexPhaseData

variable {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
  (H : HexPhaseData D P R)


@[simp] theorem toRegionAssign_lam : H.toRegionAssign.lam = H.lam := rfl

@[simp] theorem toRegionAssign_taup : H.toRegionAssign.taup = H.taup := rfl

@[simp] theorem toRegionAssign_taum : H.toRegionAssign.taum = H.taum := rfl

@[simp] theorem toRegionAssign_ups : H.toRegionAssign.ups = H.ups := rfl

@[simp] theorem toRegionAssign_Fa : H.toRegionAssign.Fa = H.Fa := rfl

end HexPhaseData


theorem hexPhase_identity {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
    (hsub : P.interior ⊆ D.incidences) (H : HexPhaseData D P R) (hFa : H.Fa = 1) :
    hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups = 1 := by
  have h := hexBdryAssign_identity hsub H.toRegionAssign (by simpa using hFa)
  simpa using h


theorem hexPhase_identity_scales {D : ℕ → HexDomain V}
    {P : ∀ v, (D v).InteriorPairing} {R : ℕ → HexRegion}
    (hsub : ∀ v, (P v).interior ⊆ (D v).incidences)
    (H : ∀ v, HexPhaseData (D v) (P v) (R v))
    (hFa : ∀ v, 1 ≤ v → (H v).Fa = 1) :
    ∀ v, 1 ≤ v →
      hexBdryCl * (H v).lam + hexBdryCt * ((H v).taup + (H v).taum) + (H v).ups = 1 := by
  intro v hv
  exact hexPhase_identity (hsub v) (H v) (hFa v hv)


theorem hexPhase_hexCell_normalForm (j : Fin 3) :
    hexUnit (2 * (j : ℤ))
      = Complex.I * Complex.exp ((-(hexPhase_sideTilt (2 * (j : ℤ))) : ℝ) * Complex.I) :=
  hexPhase_hexUnit_normalForm (2 * (j : ℤ))


theorem hexPhase_proj_fires (h : ℤ) (cmag : ℝ) :
    ((1 / 2 : ℂ) * hexUnit h)
        * (2 * Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * (cmag : ℂ))
      = Complex.I * (cmag : ℂ) :=
  hexPhase_proj h cmag _ rfl

end StatMech.Universality
