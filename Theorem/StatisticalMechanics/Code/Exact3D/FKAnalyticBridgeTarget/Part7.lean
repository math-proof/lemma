/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Structure.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget.Part3


namespace StatMech

namespace Exact3D

namespace FKMassAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


theorem hasCorrelationLength
    (T : FKMassAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.isingCorrelationLength β) :=
  T.realizesXAxisLength β hβ


theorem eventually_mem_betaLeftCriticalInterval
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3) :=
  eventually_mem_fkBetaLeftCriticalIoo T.betaδ_pos


theorem eventually_mem_pLeftCriticalInterval
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) :=
  eventually_mem_fkPLeftCriticalIoo T.pδ_pos

set_option linter.style.longLine false in


theorem eventually_pOfBeta_mem_pLeftCriticalInterval
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      IsingFK.pOfBeta β ∈
        Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) :=
  eventually_pOfBeta_mem_fkPLeftCriticalIoo T.pδ_pos


theorem betaC_sub_pos_of_mem_betaLeftCriticalInterval
    (T : FKMassAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_fkBetaLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval
    (T : FKMassAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.betaδ :=
  betaC_sub_lt_delta_of_mem_fkBetaLeftCriticalIoo hβ


theorem pCritical_sub_pos_of_mem_pLeftCriticalInterval
    (T : FKMassAnalyticRGToExponentTarget C)
    {p : ℝ}
    (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
      (IsingFK.pOfBeta (Ising.betaC 3))) :
    0 < IsingFK.pOfBeta (Ising.betaC 3) - p :=
  pCritical_sub_pos_of_mem_fkPLeftCriticalIoo hp


theorem pCritical_sub_lt_delta_of_mem_pLeftCriticalInterval
    (T : FKMassAnalyticRGToExponentTarget C)
    {p : ℝ}
    (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
      (IsingFK.pOfBeta (Ising.betaC 3))) :
    IsingFK.pOfBeta (Ising.betaC 3) - p < T.pδ :=
  pCritical_sub_lt_delta_of_mem_fkPLeftCriticalIoo hp


theorem eventually_betaC_sub_pos
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_fkBetaLeftCriticalIoo T.betaδ_pos


theorem eventually_betaC_sub_lt_delta
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.betaδ :=
  eventually_betaC_sub_lt_delta_fkBetaLeftCriticalIoo T.betaδ_pos


theorem eventually_pCritical_sub_pos
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      0 < IsingFK.pOfBeta (Ising.betaC 3) - p :=
  eventually_pCritical_sub_pos_fkPLeftCriticalIoo T.pδ_pos


theorem eventually_pCritical_sub_lt_delta
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      IsingFK.pOfBeta (Ising.betaC 3) - p < T.pδ :=
  eventually_pCritical_sub_lt_delta_fkPLeftCriticalIoo T.pδ_pos


theorem eventually_hasCorrelationLength
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.isingCorrelationLength β) := by
  filter_upwards [T.eventually_mem_betaLeftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ


theorem eventually_fkMass_pos
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      0 < T.fkMass p := by
  filter_upwards [T.eventually_mem_pLeftCriticalInterval] with p hp
  exact T.fkMass_pos p hp

set_option linter.style.longLine false in


theorem eventually_fkMass_pos_comp_pOfBeta
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.fkMass (IsingFK.pOfBeta β) := by
  filter_upwards [T.eventually_pOfBeta_mem_pLeftCriticalInterval] with β hp
  exact T.fkMass_pos (IsingFK.pOfBeta β) hp


theorem eventually_fk_length_eq_inv_mass
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      T.fkCorrelationLength p = (T.fkMass p)⁻¹ := by
  filter_upwards [T.eventually_mem_pLeftCriticalInterval] with p hp
  exact T.fk_length_eq_inv_mass p hp

set_option linter.style.longLine false in


theorem eventually_fk_length_eq_inv_mass_comp_pOfBeta
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.fkCorrelationLength (IsingFK.pOfBeta β) =
        (T.fkMass (IsingFK.pOfBeta β))⁻¹ := by
  filter_upwards [T.eventually_pOfBeta_mem_pLeftCriticalInterval] with β hp
  exact T.fk_length_eq_inv_mass (IsingFK.pOfBeta β) hp


theorem eventually_fkPrefactor_pos
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      0 < T.fkPrefactor p := by
  filter_upwards [T.eventually_mem_pLeftCriticalInterval] with p hp
  exact T.fkPrefactor_pos p hp

set_option linter.style.longLine false in


theorem eventually_fkPrefactor_pos_comp_pOfBeta
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.fkPrefactor (IsingFK.pOfBeta β) := by
  filter_upwards [T.eventually_pOfBeta_mem_pLeftCriticalInterval] with β hp
  exact T.fkPrefactor_pos (IsingFK.pOfBeta β) hp


theorem eventually_fk_length_scaling
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      T.fkCorrelationLength p =
        T.fkPrefactor p *
          Real.exp
            (-C.predictedExponent *
      Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) := by
  filter_upwards [T.eventually_mem_pLeftCriticalInterval] with p hp
  exact T.fk_length_scaling p hp

set_option linter.style.longLine false in


theorem eventually_fk_length_scaling_comp_pOfBeta
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.fkCorrelationLength (IsingFK.pOfBeta β) =
        T.fkPrefactor (IsingFK.pOfBeta β) *
          Real.exp
            (-C.predictedExponent *
              Real.log
                (IsingFK.pOfBeta (Ising.betaC 3) -
                  IsingFK.pOfBeta β)) := by
  filter_upwards [T.eventually_pOfBeta_mem_pLeftCriticalInterval] with β hp
  exact T.fk_length_scaling (IsingFK.pOfBeta β) hp


theorem eventually_ising_fk_length_agree
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.isingCorrelationLength β =
        T.fkCorrelationLength (IsingFK.pOfBeta β) :=
  T.ising_fk_length_agree


theorem fk_hasCriticalNu
    (T : FKMassAnalyticRGToExponentTarget C) :
    HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
      T.fkCorrelationLength C.predictedExponent := by
  refine _root_.StatMech.Exact3D.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo
    (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
    T.fkCorrelationLength T.fkPrefactor C.predictedExponent
    T.pδ T.pδ_pos ?_ ?_ ?_
  · intro p hp
    exact T.fkPrefactor_pos p (by simpa [ParameterModel] using hp)
  · simpa [ParameterModel] using T.fkPrefactor_log_negligible
  · intro p hp
    exact T.fk_length_scaling p (by simpa [ParameterModel] using hp)


end FKMassAnalyticRGToExponentTarget
end Exact3D
end StatMech
