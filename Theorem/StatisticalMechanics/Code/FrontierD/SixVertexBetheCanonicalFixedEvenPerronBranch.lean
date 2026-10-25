/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedEvenPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem exists_uniform_sixVertexFixedChargeDensityGaugeNumericalMargins_Ici
    {a rhoLower : Real} (ha : 2 < a) (hrhoLower : 0 < rhoLower) (r : Nat) :
    ∃ inner outer : Real,
      0 < outer ∧ inner < outer ∧
      (∀ c, a ≤ c → outer ≤ rhoLower *
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c) / 2) ∧
      ∀ᶠ N : Nat in atTop, ∀ c, a ≤ c →
        sixVertexRootDensityContractionRate c * outer +
            sixVertexFixedChargeDensityStabilityErrorOfLower
              c N r (rhoLower / 2) ≤ inner ∧
          sixVertexSymmetricScatteringBoundaryBound c +
              2 * sixVertexSymmetricJacobianTotalErrorOfLower
                c N (rhoLower / 2) < 2 * Real.pi := by
  obtain ⟨inner₀, outer, houterPos, hinner₀Outer, houter, hmargins⟩ :=
    exists_uniform_sixVertexDensityGaugeNumericalMargins_Ici ha hrhoLower
  let inner := (inner₀ + outer) / 2
  have hinner₀Inner : inner₀ < inner := by
    dsimp [inner]
    linarith
  have hinnerOuter : inner < outer := by
    dsimp [inner]
    linarith
  obtain ⟨B, hB, hBbound⟩ :=
    exists_uniformBound_sixVertexFixedChargeDensityStabilityError_Ici
      ha (by positivity : 0 < rhoLower / 2) r
  have hrate (c : Real) (hc : a ≤ c) :
      sixVertexRootDensityContractionRate c * outer ≤ inner₀ := by
    obtain ⟨N, hNmargin, hNpos⟩ :=
      (hmargins.and (eventually_gt_atTop 0)).exists
    have herror : 0 ≤
        sixVertexFiniteDensityContinuumErrorOfLower
          c N (rhoLower / 2) := by
      unfold sixVertexFiniteDensityContinuumErrorOfLower
      have hc2 : 2 < c := ha.trans_le hc
      have hNreal : (0 : Real) < N := by exact_mod_cast hNpos
      have hL : 0 ≤ sixVertexRootDensityKernelLipschitzBound c :=
        (sixVertexRootDensityKernelLipschitzBound_pos hc2).le
      have hU : 0 ≤ sixVertexFiniteRootDensityUniformBound c := by
        unfold sixVertexFiniteRootDensityUniformBound
        have hd := one_lt_sixVertexAnisotropyMagnitude hc2
        have hratio : 0 ≤ sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1) := by positivity
        exact div_nonneg (by linarith) (by positivity)
      positivity
    exact le_trans (by linarith) (hNmargin c hc).1
  have hBzero : Tendsto (fun N : Nat => B / (N : Real)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat B
  have hBsmall : ∀ᶠ N : Nat in atTop,
      B / (N : Real) < inner - inner₀ :=
    hBzero.eventually (Iio_mem_nhds (sub_pos.mpr hinner₀Inner))
  refine ⟨inner, outer, houterPos, hinnerOuter, houter, ?_⟩
  filter_upwards [hmargins, hBsmall, eventually_gt_atTop 0] with
      N hNmargin hBN hNpos
  intro c hc
  have hfixed := hBbound hNpos c hc
  constructor
  · have := hrate c hc
    linarith
  · exact (hNmargin c hc).2

theorem sixVertexFixedEvenChargeRoots_mem_open_canonical
    {c : Real} (hc : 2 < c) (s k : Nat) :
    SixVertexOpenRootSimplex (sixVertexFixedEvenChargeBetheRoots hc s k) := by
  let e : Fin ((s + k + 1) + (s + k + 1)) ≃
      Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) :=
    (Fin.castOrderIso
      (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm).toEquiv
  have h := sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k
  refine ⟨?_, sixVertexFixedEvenChargeBetheRoots_symmetric hc s k, ?_⟩
  · intro i j hij
    exact h.1 (by simpa [e] using hij)
  · intro i
    exact h.2.2 (e i)

theorem sixVertexFixedEvenChargeRoots_is_solution_canonical
    {c : Real} (hc : 2 < c) (s k : Nat) :
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth (2 * s) k)
      ((s + k + 1) + (s + k + 1))
      (sixVertexFixedEvenChargeBetheRoots hc s k) := by
  let e : Fin ((s + k + 1) + (s + k + 1)) ≃
      Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) :=
    (Fin.castOrderIso
      (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm).toEquiv
  intro j
  have hj := sixVertexFixedChargeBetheRoots_is_solution hc (2 * s) k (e j)
  have hquantum : sixVertexCentralQuantumNumber (e j) =
      sixVertexCentralQuantumNumber j := by
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp [e]
    ring
  let f : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) → Real :=
    fun l => sixVertexTheta c
      (sixVertexFixedChargeBetheRoots hc (2 * s) k (e j))
      (sixVertexFixedChargeBetheRoots hc (2 * s) k l)
  have hsum : (∑ l, f l) = ∑ l, f (e l) := by
    simpa using (Equiv.sum_comp e f).symm
  rw [hquantum] at hj
  rw [show (∑ l, sixVertexTheta c
      (sixVertexFixedChargeBetheRoots hc (2 * s) k (e j))
      (sixVertexFixedChargeBetheRoots hc (2 * s) k l)) =
        ∑ l, f l by rfl, hsum] at hj
  simpa [sixVertexFixedEvenChargeBetheRoots, e, f] using hj


end
end StatMech.FrontierD
