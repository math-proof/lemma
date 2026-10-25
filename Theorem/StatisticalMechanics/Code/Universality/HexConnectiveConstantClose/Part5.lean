/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRealizeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexZDivTauClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHammersleyWelshClose.Part2
import Def.StatisticalMechanics.Code.Universality.HexConnectiveConstantClose.Part4


namespace StatMech.Universality

open Filter Topology

open scoped Topology Real NNReal BigOperators


theorem hxf_divergence_witness :
    ¬ Summable (fun n => hxf_wc n * hexChiE ^ n) :=
  hxf_hexZ_chi_div hxf_wc hxf_wEυ hxf_wEla (fun _ => 0) (fun _ => le_refl 0)
    (fun _ => hbi_witness) (fun _ _ => rfl)
    (fun v => (hxf_wEla_lamCum v).symm) (fun _ => rfl) (fun v => (hxf_wEυ_fiberSum v).symm)
    (fun _ => hxf_wCut) hxf_wEB
    (fun v _ => by show (1:ℝ) = hxf_wc (v + 1) * hexChiE ^ (v + 1); rw [hxf_wc_wt])
    hxf_wED (fun _ d => d.elim)
    (fun v _ => by rw [hxf_wEυ_fiberSum]; norm_num)
    hxf_wSide rfl rfl


theorem hxf_divergence_witness_consistent : ¬ Summable (fun _ : ℕ => (1:ℝ)) := by
  have h := hxf_divergence_witness
  have heq : (fun n => hxf_wc n * hexChiE ^ n) = (fun _ : ℕ => (1:ℝ)) := by
    funext n; exact hxf_wc_wt n
  rwa [heq] at h


theorem hxf_wc_saw_facts :
    (∀ n, 1 ≤ hxf_wc n) ∧ Submultiplicative hxf_wc := by
  refine ⟨fun n => ?_, fun m n => ?_⟩
  · exact one_le_pow₀ hxf_one_le_chiInv
  · show (hexChiE⁻¹) ^ (m + n) ≤ (hexChiE⁻¹) ^ m * (hexChiE⁻¹) ^ n
    rw [pow_add]

end StatMech.Universality
