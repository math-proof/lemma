/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17


namespace StatMech

namespace Exact3D

theorem eventually_mem_fkBetaLeftCriticalIoo {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) := by
  filter_upwards
    [Ioo_mem_nhdsLT (show Ising.betaC 3 - δ < Ising.betaC 3 by
      linarith)] with β hβ
  exact hβ


theorem betaC_sub_pos_of_mem_fkBetaLeftCriticalIoo
    {δ β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  sub_pos.mpr hβ.2


theorem betaC_sub_lt_delta_of_mem_fkBetaLeftCriticalIoo
    {δ β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < δ := by
  linarith [hβ.1]


theorem beta_pos_of_mem_fkBetaLeftCriticalIoo_of_delta_le_betaC
    {δ β : ℝ} (hδle : δ ≤ Ising.betaC 3)
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
    0 < β := by
  have hnonneg : 0 ≤ Ising.betaC 3 - δ := sub_nonneg.mpr hδle
  linarith [hβ.1, hnonneg]


theorem eventually_betaC_sub_pos_fkBetaLeftCriticalIoo {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β := by
  filter_upwards [eventually_mem_fkBetaLeftCriticalIoo hδ] with β hβ
  exact betaC_sub_pos_of_mem_fkBetaLeftCriticalIoo hβ


theorem eventually_betaC_sub_lt_delta_fkBetaLeftCriticalIoo {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < δ := by
  filter_upwards [eventually_mem_fkBetaLeftCriticalIoo hδ] with β hβ
  exact betaC_sub_lt_delta_of_mem_fkBetaLeftCriticalIoo hβ


theorem eventually_mem_fkPLeftCriticalIoo {pδ : ℝ} (hpδ : 0 < pδ) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) := by
  filter_upwards
    [Ioo_mem_nhdsLT
      (show IsingFK.pOfBeta (Ising.betaC 3) - pδ <
          IsingFK.pOfBeta (Ising.betaC 3) by
        linarith)] with p hp
  exact hp

set_option linter.style.longLine false in

theorem eventually_pOfBeta_mem_fkPLeftCriticalIoo {pδ : ℝ}
    (hpδ : 0 < pδ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      IsingFK.pOfBeta β ∈
        Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) :=
  FKReparameterization.eventually_pOfBeta_mem_Ioo_left
    (βc := Ising.betaC 3) hpδ


theorem pCritical_sub_pos_of_mem_fkPLeftCriticalIoo
    {pδ p : ℝ}
    (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
      (IsingFK.pOfBeta (Ising.betaC 3))) :
    0 < IsingFK.pOfBeta (Ising.betaC 3) - p :=
  sub_pos.mpr hp.2


theorem pCritical_sub_lt_delta_of_mem_fkPLeftCriticalIoo
    {pδ p : ℝ}
    (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
      (IsingFK.pOfBeta (Ising.betaC 3))) :
    IsingFK.pOfBeta (Ising.betaC 3) - p < pδ := by
  linarith [hp.1]


theorem eventually_pCritical_sub_pos_fkPLeftCriticalIoo {pδ : ℝ}
    (hpδ : 0 < pδ) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      0 < IsingFK.pOfBeta (Ising.betaC 3) - p := by
  filter_upwards [eventually_mem_fkPLeftCriticalIoo hpδ] with p hp
  exact pCritical_sub_pos_of_mem_fkPLeftCriticalIoo hp


theorem eventually_pCritical_sub_lt_delta_fkPLeftCriticalIoo {pδ : ℝ}
    (hpδ : 0 < pδ) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      IsingFK.pOfBeta (Ising.betaC 3) - p < pδ := by
  filter_upwards [eventually_mem_fkPLeftCriticalIoo hpδ] with p hp
  exact pCritical_sub_lt_delta_of_mem_fkPLeftCriticalIoo hp


theorem hasCriticalNu_comp_pOfBeta_congr_eventually
    {βc ν : ℝ} {fkCorrelationLength comparisonLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta βc))
        fkCorrelationLength ν)
    (hEq :
      ∀ᶠ β in nhdsWithin βc (Set.Iio βc),
        comparisonLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu (ParameterModel βc) comparisonLength ν :=
  FKReparameterization.hasCriticalNu_comp_pOfBeta_congr_eventually hfk hEq

namespace RGCertificate


theorem rgToExponentBridge_of_fk_pOfBeta_eventually_eq
    (C : RGCertificate Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    C.RGToExponentBridge isingCorrelationLength :=
  C.rgToExponentBridge_of_hasCriticalNu isingCorrelationLength
    ((hasCriticalNu_comp_pOfBeta_congr_eventually hfk hEq).congr_betaC (by rfl))


theorem rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (C : RGCertificate Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (C.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    C.RGToExponentBridge isingCorrelationLength :=
  C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq
    (by simpa [RGToExponentBridge] using hfk) hEq


theorem
    rgToExponentBridge_of_fk_pOfBeta_retargetBridge_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent)
    (hfk :
      (D.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    C.RGToExponentBridge isingCorrelationLength := by
  have hfkC :
      (C.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength :=
    RGCertificate.rgToExponentBridge_congr_predictedExponent hfk (by
      simpa using hpred)
  exact
    C.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
      hfkC hEq


theorem valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (C : RGCertificate Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (C.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
      hfk hEq)


theorem
    valid_of_fk_pOfBeta_retargetBridge_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent)
    (hfk :
      (D.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_pOfBeta_retargetBridge_congr_predictedExponent
      hpred hfk hEq)


theorem valid_of_fk_pOfBeta_eventually_eq
    (C : RGCertificate Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq)


theorem hasCriticalNu_of_fk_pOfBeta_eventually_eq
    (C : RGCertificate Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq


theorem rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    C.RGToExponentBridge isingCorrelationLength :=
  C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq
    (by simpa [hpred] using hfk) hEq


theorem valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
      hpred hfk hEq)


theorem hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    hpred hfk hEq


theorem hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (C : RGCertificate Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (C.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq hfk hEq


theorem
    hasCriticalNu_of_fk_pOfBeta_retargetBridge_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent)
    (hfk :
      (D.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_pOfBeta_retargetBridge_congr_predictedExponent
    hpred hfk hEq


theorem rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    (C : RGCertificate Ising3DModel)
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hscaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-C.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    C.RGToExponentBridge isingCorrelationLength := by
  have hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent := by
    refine _root_.StatMech.Exact3D.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo
      (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
      fkCorrelationLength fkPrefactor C.predictedExponent pδ hpδ ?_ ?_ ?_
    · intro p hp
      exact hpref_pos p (by simpa [ParameterModel] using hp)
    · simpa [ParameterModel] using hlogpref
    · intro p hp
      exact hscaling p (by simpa [ParameterModel] using hp)
  exact C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq


theorem valid_of_fk_exact_power_variable_prefactor_on_Ioo
    (C : RGCertificate Ising3DModel)
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hscaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-C.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
      isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ
      hpref_pos hlogpref hscaling hEq)


theorem hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo
    (C : RGCertificate Ising3DModel)
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hscaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-C.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ
    hpref_pos hlogpref hscaling hEq


theorem
    rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hscaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    C.RGToExponentBridge isingCorrelationLength :=
  C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ
    hpref_pos hlogpref
    (fun p hp => by simpa [hpred] using hscaling p hp)
    hEq


theorem
    valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hscaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkPrefactor hpred pδ hpδ
      hpref_pos hlogpref hscaling hEq)


theorem
    hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hscaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkPrefactor hpred pδ hpδ
    hpref_pos hlogpref hscaling hEq


theorem rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (C : RGCertificate Ising3DModel)
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkMassPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkMassPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hmass_scaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (C.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    C.RGToExponentBridge isingCorrelationLength := by
  have hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent := by
    refine _root_.StatMech.Exact3D.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo
      (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
      fkCorrelationLength fkMass fkMassPrefactor C.predictedExponent
      pδ hpδ ?_ ?_ ?_ ?_
    · intro p hp
      exact hpref_pos p (by simpa [ParameterModel] using hp)
    · simpa [ParameterModel] using hlogpref
    · intro p hp
      exact hmass_scaling p (by simpa [ParameterModel] using hp)
    · intro p hp
      exact hfk_length_eq_inv_mass p (by simpa [ParameterModel] using hp)
  exact C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq


theorem valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (C : RGCertificate Ising3DModel)
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkMassPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkMassPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hmass_scaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (C.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq)


theorem hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (C : RGCertificate Ising3DModel)
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkMassPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkMassPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hmass_scaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (C.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq


theorem
    rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkMassPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkMassPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hmass_scaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    C.RGToExponentBridge isingCorrelationLength :=
  C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pδ hpδ hpref_pos hlogpref
    (fun p hp => by simpa [hpred] using hmass_scaling p hp)
    hfk_length_eq_inv_mass hEq


theorem
    valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkMassPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkMassPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hmass_scaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      hpred pδ hpδ hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)


theorem
    hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkMassPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkMassPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hmass_scaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    hpred pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass
    hEq

end RGCertificate
end Exact3D
end StatMech
