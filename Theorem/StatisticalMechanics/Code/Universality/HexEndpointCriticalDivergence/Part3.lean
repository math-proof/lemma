/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCriticalDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Structure.StatisticalMechanics.Code.Universality.HexEndpointCriticalDivergence.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hecd_side_limit_forces_walk_divergence
    {a : ℂ} {h0 : ℤ} {tau : ℕ → ℝ}
    (S : HexEndpointSideLimits a h0 tau)
    (hpos : ∃ T, 1 ≤ T ∧ 0 < tau T) :
    ¬ Summable (hexEndpointSAWwt a h0 hexChiE) := by
  rintro hwalk
  obtain ⟨T, _, hTpos⟩ := hpos
  have hfib : Summable (S.fibers.columnEmb T).fiberSum :=
    (S.fibers.columnEmb T).fiberSum_summable hwalk
  have hzero := hfib.tendsto_atTop_zero
  have : tau T = 0 := tendsto_nhds_unique (S.tendsto_tau T) hzero
  exact (ne_of_gt hTpos) this


theorem hecd_critical_divergence_of_recurrence
    (a : ℂ) (h0 : ℤ)
    (lam tau : ℕ → ℝ)
    (Pcol : List ℤ → Prop)
    (scale : {ts : List ℤ // Pcol ts} → ℕ)
    (S : HexEndpointSideLimits a h0 tau)
    (hbdry : ∀ v, 1 ≤ v →
      hexCl * lam v + hexCt * tau v +
        hecd_columnSum a h0 Pcol scale v = 1)
    (hrec : ∀ v, 1 ≤ v →
      lam (v + 1) - lam v ≤
        hexChiE⁻¹ * (hecd_columnSum a h0 Pcol scale (v + 1)) ^ 2)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hcolPos : ∀ v, 1 ≤ v → 0 < hecd_columnSum a h0 Pcol scale v)
    (hτnn : ∀ v, 0 ≤ tau v) :
    ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) := by
  have hτcol : (∃ v, 1 ≤ v ∧ 0 < tau v) →
      ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) := by
    intro hpos
    exact hexEndpoint_hlc_not_summable_of_walk a h0 hexChiE_pos
      (hecd_side_limit_forces_walk_divergence S hpos)
  have hcolEmb :
      Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) →
        Summable (hecd_columnSum a h0 Pcol scale) := by
    intro hcoeff
    have hwalk : Summable (hexEndpointSAWwt a h0 hexChiE) :=
      (hexEndpoint_walk_summable_iff_hlc a h0 hexChiE_pos).2 hcoeff
    exact hecd_columnSum_summable a h0 Pcol scale hwalk
  exact hexZ_chi_div_recon (hlc_sawCountR a h0) lam tau
    (hecd_columnSum a h0 Pcol scale) hbdry hrec hlamMono hcolPos
    (hecd_columnSum_nonneg a h0 Pcol scale) hτnn hτcol hcolEmb

end
end StatMech.Universality
