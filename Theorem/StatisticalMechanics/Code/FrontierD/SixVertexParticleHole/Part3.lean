/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part2
open Finset Matrix


namespace StatMech.FrontierD

theorem sixVertexSectorPrefixForward_of_positions {N n : ℕ}
    (x y : SixVertexSector N n) (h : SixVertexPositionsForwardInterlaced x y) :
    SixVertexSectorPrefixForward x y := by
  intro k
  let px := sixVertexSectorPrefixCount x k
  let py := sixVertexSectorPrefixCount y k
  constructor
  · by_contra! hbad
    have hpyn : py ≤ n := sixVertexSectorPrefixCount_le_card y k
    let i : Fin n := ⟨px, lt_of_lt_of_le hbad hpyn⟩
    have hyk : sixVertexSectorPosition y i ≤ k := by
      apply (sixVertexSectorPosition_le_iff_lt_prefixCount y i k).mpr
      exact hbad
    have hxk : sixVertexSectorPosition x i ≤ k := (h.1 i).trans hyk
    have := (sixVertexSectorPosition_le_iff_lt_prefixCount x i k).mp hxk
    exact (Nat.lt_irrefl px) this
  · by_contra! hbad
    have hpxn : px ≤ n := sixVertexSectorPrefixCount_le_card x k
    have hpylt : py + 1 < n := lt_of_lt_of_le hbad hpxn
    let i : Fin n := ⟨py + 1, hpylt⟩
    have hxk : sixVertexSectorPosition x i ≤ k := by
      apply (sixVertexSectorPosition_le_iff_lt_prefixCount x i k).mpr
      exact hbad
    have hcross := h.2 py (by omega)
    have hyk : sixVertexSectorPosition y ⟨py, by omega⟩ ≤ k := by
      exact hcross.trans hxk
    have := (sixVertexSectorPosition_le_iff_lt_prefixCount y
      ⟨py, by omega⟩ k).mp hyk
    exact (Nat.lt_irrefl py) this

theorem sixVertexPositionsForwardInterlaced_of_prefix {N n : ℕ}
    (x y : SixVertexSector N n) (h : SixVertexSectorPrefixForward x y) :
    SixVertexPositionsForwardInterlaced x y := by
  constructor
  · intro i
    let k := sixVertexSectorPosition y i
    apply (sixVertexSectorPosition_le_iff_lt_prefixCount x i k).mpr
    have hy : sixVertexSectorPrefixCount y k = i.val + 1 :=
      sixVertexSectorPrefixCount_at_position y i
    have hle := (h k).1
    omega
  · intro k hk
    let i : Fin n := ⟨k + 1, hk⟩
    let p := sixVertexSectorPosition x i
    apply (sixVertexSectorPosition_le_iff_lt_prefixCount y ⟨k, by omega⟩ p).mpr
    have hx : sixVertexSectorPrefixCount x p = k + 2 := by
      simpa [i] using sixVertexSectorPrefixCount_at_position x i
    have hle := (h p).2
    change k < sixVertexSectorPrefixCount y p
    omega


end StatMech.FrontierD
