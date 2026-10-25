/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexColumnMembershipClose.Part2


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


theorem hcm_take_spans (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ) (cp : ℕ)
    (hT : (T : ℝ) ≤ hexW2_partialDisp h0 ts cp - (HexWalk.halfStep h0).re) :
    hcm_SpansWidth a h0 T (ts.take cp) := by
  refine ⟨a + halfStep h0, hcm_first_vertex_mem a h0 (ts.take cp),
    hexInfra_midAccum a h0 (ts.take cp) + halfStep (hexInfra_headAccum h0 (ts.take cp)), ?_, ?_⟩
  · exact hexInfra_verticesAux_getLast_mem a h0 (ts.take cp)
  · rw [hexInfra_ofTurns_last_re a h0 (ts.take cp), Complex.add_re]
    unfold hexW2_partialDisp at hT
    linarith


theorem hcm_drop_first_is_max (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ)
    (hcp : cp = hexW2_cutPos h0 ts) (hcple : cp ≤ ts.length) :
    ∀ v ∈ (HexWalk.ofTurns (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp))
        (ts.drop cp)).vertices,
      v.re ≤ (hfs_stMid a h0 (ts.take cp)).re
        + (HexWalk.halfStep (hfs_stHead h0 (ts.take cp))).re := by
  intro v hvmem
  rw [show (HexWalk.ofTurns (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp))
      (ts.drop cp)).vertices = (verticesAux a h0 ts).drop cp from ?_] at hvmem
  · have hvfull : v ∈ verticesAux a h0 ts := List.mem_of_mem_drop hvmem
    have hbound := hcm_vertex_re_le_cutDisp a h0 ts v hvfull
    have hstart := hcm_dropStart_re a h0 ts cp
    rw [← hcp] at hbound
    rw [hstart]; linarith
  · unfold HexWalk.ofTurns HexWalk.vertices
    simp only
    exact hfs_verticesAux_drop a h0 ts cp (hcp ▸ hcple)


theorem hcm_drop_not_reaches (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (cp : ℕ) (hcp : cp = hexW2_cutPos h0 ts) (hcple : cp ≤ ts.length) (T : ℕ) (hT : 1 ≤ T) :
    ¬ hexWall3_ReachesWidth (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp))
        T (ts.drop cp) := by
  rintro ⟨v, hvmem, hvre⟩
  have hmax := hcm_drop_first_is_max a h0 ts cp hcp hcple v hvmem
  have hhalf := hexInfra_halfStep_re_le (hfs_stHead h0 (ts.take cp))
  have hTr : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  
  linarith


theorem hcm_drop_spans (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ) (cp : ℕ)
    (hdescend : (T : ℝ)
      ≤ (HexWalk.halfStep (hexInfra_headAccum h0 (ts.take cp))).re
        - (hexInfra_stepReSum (hexInfra_headAccum h0 (ts.take cp)) (ts.drop cp)
            + (HexWalk.halfStep
                (hexInfra_headAccum (hexInfra_headAccum h0 (ts.take cp)) (ts.drop cp))).re)) :
    hcm_SpansWidth (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp)) T (ts.drop cp) := by
  set m := hfs_stMid a h0 (ts.take cp) with hmdef
  set h := hfs_stHead h0 (ts.take cp) with hhdef
  have hh : h = hexInfra_headAccum h0 (ts.take cp) := hcm_stHead_eq_headAccum h0 (ts.take cp)
  have hm : m.re = a.re + hexInfra_stepReSum h0 (ts.take cp) := by
    rw [hmdef, hcm_stMid_eq_midAccum]; rw [hexInfra_midAccum_re]
  refine ⟨hexInfra_midAccum m h (ts.drop cp) + halfStep (hexInfra_headAccum h (ts.drop cp)), ?_,
          m + halfStep h, ?_, ?_⟩
  · unfold HexWalk.ofTurns HexWalk.vertices; simp only
    exact hexInfra_verticesAux_getLast_mem m h (ts.drop cp)
  · unfold HexWalk.ofTurns HexWalk.vertices; simp only; exact hcm_first_vertex_mem m h (ts.drop cp)
  · rw [Complex.add_re, Complex.add_re, hexInfra_midAccum_re, hm, hh]
    linarith [hdescend]


end StatMech.Universality
