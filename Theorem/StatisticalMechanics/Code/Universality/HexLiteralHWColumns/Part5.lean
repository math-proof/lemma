/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part6
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem HLHCMidpointColumnWalk.midCoord_mem_vertexSet
    {T : ℕ} {ts : List ℤ} (W : HLHCMidpointColumnWalk T ts)
    (k : Fin ts.length) :
    W.midCoord k ∈ hexCSVertexSet T W.stripHeight := by
  rw [hexCS_mem_vertexSet_iff]
  refine ⟨(W.horizontal k).1, (W.horizontal k).2, ?_, ?_⟩
  · exact le_trans (hlhc_coord_le_bound_i _)
      (by
        exact_mod_cast le_trans
          (Finset.le_sup (f := fun n : Fin ts.length =>
            hlhc_coordBound (W.midCoord n)) (Finset.mem_univ k))
          (Nat.le_max_left _ _))
  · exact le_trans (hlhc_coord_le_bound_j _)
      (by
        exact_mod_cast le_trans
          (Finset.le_sup (f := fun n : Fin ts.length =>
            hlhc_coordBound (W.midCoord n)) (Finset.mem_univ k))
          (Nat.le_max_left _ _))

theorem HLHCMidpointColumnWalk.top_mem_vertexSet
    {T : ℕ} {ts : List ℤ} (W : HLHCMidpointColumnWalk T ts)
    (hT : 0 < T) :
    W.topCoord ∈ hexCSVertexSet T W.stripHeight := by
  rw [hexCS_mem_vertexSet_iff]
  have hbook : hexAWBookRe2 W.topCoord = 3 * T - 1 := by
    simp [hexAWBookRe2, W.top_white, W.top_depth]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hbook]
    omega
  · rw [hbook]
    omega
  · exact le_trans (hlhc_coord_le_bound_i _)
      (by exact_mod_cast Nat.le_max_right _ _)
  · exact le_trans (hlhc_coord_le_bound_j _)
      (by exact_mod_cast Nat.le_max_right _ _)


theorem HLHCMidpointColumnWalk.mem_topAtWidth
    {T : ℕ} {ts : List ℤ} (W : HLHCMidpointColumnWalk T ts)
    (hT : 0 < T) : HexCSTopWalkAtWidth T hT ts := by
  refine ⟨W.stripHeight, W.legal, ?_,
    W.topCoord, W.top_mem_vertexSet hT, W.top_white, W.top_depth, W.endsAt⟩
  intro z hz
  unfold HexWalk.mids at hz
  change z ∈ midsAux hexAWStart 1 ts at hz
  rw [List.mem_iff_getElem] at hz
  obtain ⟨k, hklen, hkz⟩ := hz
  have hkle : k ≤ ts.length := by
    rw [length_midsAux] at hklen
    omega
  have hget := hexJordan_midsAux_getElem?_eq hexAWStart 1 ts k hkle
  rw [List.getElem?_eq_getElem hklen, Option.some.injEq] at hget
  have hmid : hexInfra_midAccum hexAWStart 1 (ts.take k) = z :=
    hget.symm.trans hkz
  change z ∈ hexCSMids T W.stripHeight
  by_cases hk : k < ts.length
  · let k' : Fin ts.length := ⟨k, hk⟩
    rw [← hmid, W.incident k', hexCSMids, Finset.mem_biUnion]
    refine ⟨⟨W.midCoord k', W.midCoord_mem_vertexSet k'⟩,
      Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨W.midEdge k', Finset.mem_univ _, rfl⟩
  · have hkeq : k = ts.length := by omega
    have hzTop : z = hexAWMid W.topCoord 0 := by
      rw [← hmid, hkeq, List.take_length]
      rw [← hexInfra_endMid_eq_midAccum hexAWStart 1 ts]
      exact W.endsAt
    rw [hzTop, hexCSMids, Finset.mem_biUnion]
    refine ⟨⟨W.topCoord, W.top_mem_vertexSet hT⟩,
      Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨0, Finset.mem_univ _, rfl⟩

end
end StatMech.Universality
