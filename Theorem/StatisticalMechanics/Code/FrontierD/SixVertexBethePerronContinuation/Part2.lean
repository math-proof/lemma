/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part2
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorNoAdjacent_pair_of_forward_disjoint
    {N n : Nat} (x y : SixVertexSector N n)
    (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y))
    (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N))) :
    SixVertexSectorNoAdjacent x ∧ SixVertexSectorNoAdjacent y := by
  have hpos := (sixVertexForwardInterlaced_iff_positions x y).mp hforward
  have hne (i j : Fin n) :
      sixVertexSectorPosition x i ≠ sixVertexSectorPosition y j := by
    intro heq
    rw [Finset.disjoint_left] at hdisj
    exact hdisj (sixVertexSectorPosition_mem x i)
      (heq ▸ sixVertexSectorPosition_mem y j)
  constructor
  · constructor
    · intro k hk
      let i : Fin n := ⟨k, by omega⟩
      let j : Fin n := ⟨k + 1, hk⟩
      have hleft := hpos.1 i
      have hright := hpos.2 k hk
      have hleft' : (sixVertexSectorPosition x i).val <
          (sixVertexSectorPosition y i).val := by
        exact_mod_cast lt_of_le_of_ne hleft (hne i i)
      have hright' : (sixVertexSectorPosition y i).val <
          (sixVertexSectorPosition x j).val := by
        exact_mod_cast lt_of_le_of_ne hright (Ne.symm (hne j i))
      change (sixVertexSectorPosition x i).val + 1 <
        (sixVertexSectorPosition x j).val
      omega
    · intro hn
      let last : Fin n := ⟨n - 1, by omega⟩
      have hlast := hpos.1 last
      have hlast' : (sixVertexSectorPosition x last).val <
          (sixVertexSectorPosition y last).val := by
        exact_mod_cast lt_of_le_of_ne hlast (hne last last)
      have hyN := (sixVertexSectorPosition y last).isLt
      change (sixVertexSectorPosition x last).val + 1 <
        N + (sixVertexSectorPosition x ⟨0, hn⟩).val
      exact lt_of_lt_of_le
        (lt_of_le_of_lt (Nat.succ_le_of_lt hlast') hyN)
        (Nat.le_add_right N _)
  · constructor
    · intro k hk
      let i : Fin n := ⟨k, by omega⟩
      let j : Fin n := ⟨k + 1, hk⟩
      have hleft := hpos.2 k hk
      have hright := hpos.1 j
      have hleft' : (sixVertexSectorPosition y i).val <
          (sixVertexSectorPosition x j).val := by
        exact_mod_cast lt_of_le_of_ne hleft (Ne.symm (hne j i))
      have hright' : (sixVertexSectorPosition x j).val <
          (sixVertexSectorPosition y j).val := by
        exact_mod_cast lt_of_le_of_ne hright (hne j j)
      change (sixVertexSectorPosition y i).val + 1 <
        (sixVertexSectorPosition y j).val
      omega
    · intro hn
      let first : Fin n := ⟨0, hn⟩
      have hfirst := hpos.1 first
      have hfirst' : (sixVertexSectorPosition x first).val <
          (sixVertexSectorPosition y first).val := by
        exact_mod_cast lt_of_le_of_ne hfirst (hne first first)
      have hlastN := (sixVertexSectorPosition y
        ⟨n - 1, by omega⟩).isLt
      have hyfirst : 0 < (sixVertexSectorPosition y first).val :=
        lt_of_le_of_lt (Nat.zero_le _) hfirst'
      change (sixVertexSectorPosition y ⟨n - 1, by omega⟩).val + 1 <
        N + (sixVertexSectorPosition y first).val
      exact lt_of_le_of_lt (Nat.succ_le_of_lt hlastN)
        (Nat.lt_add_of_pos_right hyfirst)

theorem tendsto_sixVertexAnisotropyDenominator :
    Tendsto (fun c : Real => c ^ 2 - 2) atTop atTop := by
  have hsq : Tendsto (fun c : Real => c * c) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with c hc
    have hc1 : 1 ≤ c := le_trans (le_max_left _ _) hc
    have hcb : b ≤ c := le_trans (le_max_right _ _) hc
    nlinarith
  simpa only [pow_two, sub_eq_add_neg] using
    (tendsto_atTop_add_const_right atTop (-2) hsq)

theorem tendsto_sixVertexAnisotropyCorrection :
    Tendsto (fun c : Real => c ^ 2 / (c ^ 2 - 2)) atTop (nhds 1) := by
  have hzero : Tendsto (fun c : Real => 2 / (c ^ 2 - 2)) atTop (nhds 0) :=
    tendsto_sixVertexAnisotropyDenominator.const_div_atTop 2
  have hone : Tendsto (fun c : Real => 1 + 2 / (c ^ 2 - 2))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hzero
  apply hone.congr'
  filter_upwards
    [tendsto_sixVertexAnisotropyDenominator.eventually
      (eventually_gt_atTop (0 : Real))] with c hc
  field_simp [hc.ne']
  ring


theorem tendsto_sixVertexAnisotropyPowerRatio
    {d n : Nat} (hd : d ≤ 2 * n) :
    Tendsto (fun c : Real => c ^ d / (c ^ 2 - 2) ^ n) atTop
      (nhds (if d = 2 * n then 1 else 0)) := by
  have hcorrection :
      Tendsto (fun c : Real => c ^ (2 * n) / (c ^ 2 - 2) ^ n)
        atTop (nhds 1) := by
    simpa only [pow_mul, div_pow, one_pow] using
      tendsto_sixVertexAnisotropyCorrection.pow n
  by_cases hmax : d = 2 * n
  · subst d
    simpa using hcorrection
  · have hdlt : d < 2 * n := lt_of_le_of_ne hd hmax
    have hsmall : Tendsto (fun c : Real => c ^ d / c ^ (2 * n))
        atTop (nhds 0) :=
      tendsto_pow_div_pow_atTop_zero hdlt
    have hmul := hsmall.mul hcorrection
    have hmul' : Tendsto
        (fun c : Real => (c ^ d / c ^ (2 * n)) *
          (c ^ (2 * n) / (c ^ 2 - 2) ^ n)) atTop (nhds 0) := by
      simpa using hmul
    simp only [hmax, if_false]
    apply hmul'.congr'
    filter_upwards
      [eventually_gt_atTop (0 : Real),
        tendsto_sixVertexAnisotropyDenominator.eventually
          (eventually_gt_atTop (0 : Real))] with c hc hcden
    field_simp [hc.ne', hcden.ne']


theorem tendsto_sixVertexSectorTransfer_normalized_atTop
    {N n : Nat} (hn : 0 < n) (x y : SixVertexSector N n) :
    Tendsto (fun c : Real =>
        sixVertexSectorTransfer N n c x y / (c ^ 2 - 2) ^ n)
      atTop (nhds (sixVertexSectorTransferInfinity N n x y)) := by
  rw [sixVertexSectorTransferInfinity_apply]
  by_cases hxy : x = y
  · subst y
    have hratio := tendsto_sixVertexAnisotropyPowerRatio
      (d := 0) (n := n) (by omega)
    have hconst : Tendsto (fun _ : Real => (2 : Real)) atTop (nhds 2) :=
      tendsto_const_nhds
    have hscaled := hconst.mul hratio
    simpa [sixVertexSectorTransfer, sixVertexTransfer, hn.ne'] using hscaled
  · have hrow : sixVertexSectorRow x ≠ sixVertexSectorRow y :=
      fun h => hxy (sixVertexSectorRow_injective h)
    by_cases hinter : SixVertexInterlaced (sixVertexSectorRow x)
        (sixVertexSectorRow y)
    · have hratio := tendsto_sixVertexAnisotropyPowerRatio
        (sixVertexSectorRowDistance_le_twice N n x y)
      simpa [sixVertexSectorTransfer, sixVertexTransfer, hxy, hrow,
        hinter] using hratio
    · simp [sixVertexSectorTransfer, sixVertexTransfer, hxy, hrow,
        hinter, tendsto_const_nhds]


end
end StatMech.FrontierD
