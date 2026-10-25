/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part14
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part4


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexCSTopWalk_finset_fits
    {T : ℕ} {hT : 0 < T}
    (s : Finset {ts : List ℤ // HexCSTopWalkAtWidth T hT ts})
    (w : {ts : List ℤ // HexCSTopWalkAtWidth T hT ts})
    (hw : w ∈ s) :
    HexCSTopWalk T (hexCSTopFinsetHeight s) hT w.1 := by
  apply hexCSTopWalk_mono_L
    (Finset.le_sup (f := hexCSTopWalkHeight) hw)
  exact hexCSTopWalkHeight_spec w

theorem hexAWNeighbor_color_ne (c : HexAWCoord) (e : Fin 3) :
    (hexAWNeighbor c e).color ≠ c.color := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;> simp [hexAWNeighbor]


theorem hexAWMid_white_injective
    {c d : HexAWCoord} {e f : Fin 3}
    (hc : c.color = .white) (hd : d.color = .white)
    (hm : hexAWMid c e = hexAWMid d f) :
    c = d ∧ e = f := by
  rcases (hexAWMid_eq_iff c d e f).mp hm with
    ⟨hdc, hfe⟩ | ⟨hdc, hfe⟩
  · exact ⟨hdc.symm, hfe.symm⟩
  · exfalso
    apply hexAWNeighbor_color_ne c e
    calc
      (hexAWNeighbor c e).color = d.color :=
        congrArg HexAWCoord.color hdc.symm
      _ = .white := hd
      _ = c.color := hc.symm


theorem hexCSSlantWalk_height_unique
    {T L L' : ℕ} {hT : 0 < T} {ts : List ℤ}
    (hL : HexCSSlantWalk T L hT ts)
    (hL' : HexCSSlantWalk T L' hT ts) :
    L = L' := by
  rcases hL with ⟨_, _, c, _, hc, hside⟩
  rcases hL' with ⟨_, _, d, _, hd, hside'⟩
  rcases hside with ⟨hci, hend⟩ | ⟨hcj, hend⟩ <;>
    rcases hside' with ⟨hdi, hend'⟩ | ⟨hdj, hend'⟩
  · have hm : hexAWMid c 1 = hexAWMid d 1 := hend.symm.trans hend'
    obtain ⟨hcd, _⟩ := hexAWMid_white_injective hc hd hm
    rw [hcd] at hci
    omega
  · have hm : hexAWMid c 1 = hexAWMid d 2 := hend.symm.trans hend'
    have hedge := (hexAWMid_white_injective hc hd hm).2
    omega
  · have hm : hexAWMid c 2 = hexAWMid d 1 := hend.symm.trans hend'
    have hedge := (hexAWMid_white_injective hc hd hm).2
    omega
  · have hm : hexAWMid c 2 = hexAWMid d 2 := hend.symm.trans hend'
    obtain ⟨hcd, _⟩ := hexAWMid_white_injective hc hd hm
    rw [hcd] at hcj
    omega


end
end StatMech.Universality
