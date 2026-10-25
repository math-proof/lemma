/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part6
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part4


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem HLHCCanonicalColumnWalk.prefix_mem_vertexSet
    {T : ℕ} {ts : List ℤ} (W : HLHCCanonicalColumnWalk T ts)
    {k : ℕ} (hk : k < ts.length) :
    hlhc_prefixCoord ts W.legal.1 k ∈
      hexCSVertexSet T W.stripHeight := by
  rw [hexCS_mem_vertexSet_iff]
  refine ⟨(W.horizontal k hk).1, (W.horizontal k hk).2, ?_, ?_⟩
  · exact le_trans (hlhc_coord_le_bound_i _)
      (by
        exact_mod_cast le_trans
          (Finset.le_sup (f := fun n =>
            hlhc_coordBound (hlhc_prefixCoord ts W.legal.1 n))
            (Finset.mem_range.mpr hk))
          (Nat.le_max_left _ _))
  · exact le_trans (hlhc_coord_le_bound_j _)
      (by
        exact_mod_cast le_trans
          (Finset.le_sup (f := fun n =>
            hlhc_coordBound (hlhc_prefixCoord ts W.legal.1 n))
            (Finset.mem_range.mpr hk))
          (Nat.le_max_left _ _))

theorem HLHCCanonicalColumnWalk.top_mem_vertexSet
    {T : ℕ} {ts : List ℤ} (W : HLHCCanonicalColumnWalk T ts)
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

theorem HexWalk.IsLegalSAW.endpointIsLegalSAW {w : HexWalk}
    (h : w.IsLegalSAW) : w.EndpointIsLegalSAW := by
  exact ⟨h.1, List.Nodup.sublist (List.dropLast_sublist _) h.2⟩


theorem HLHCCanonicalColumnWalk.mem_topAtWidth
    {T : ℕ} {ts : List ℤ} (W : HLHCCanonicalColumnWalk T ts)
    (hT : 0 < T) : HexCSTopWalkAtWidth T hT ts := by
  refine ⟨W.stripHeight, W.legal.endpointIsLegalSAW, ?_,
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
  · obtain ⟨e, he⟩ := hlhc_prefixCoord_mid_incident ts W.legal.1 k
    rw [← hmid] 
    rw [hexCSMids, Finset.mem_biUnion]
    refine ⟨⟨hlhc_prefixCoord ts W.legal.1 k,
      W.prefix_mem_vertexSet hk⟩, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨e, Finset.mem_univ _, he.symm⟩
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
