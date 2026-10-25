/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.EpsToZeroLattice
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Instance.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation FieldGhostDict


theorem sctInternalBoundaryCorr_eq_ambient {d n : ℕ} (beta : ℝ)
    (T : Finset (sctBox d n)) :
    sctInternalBoundaryCorr d beta n T =
      ∑ e ∈ (boundaryEdges d (sctCutSites T)).filter
          (fun e => e.2 ∈ box d n),
        corrOriginInner d beta (sctCutSites T) e.1 := by
  classical
  let C := (sctBoxGraph d n).edgeFinset.filter (sctCrossesCut T)
  let B := (boundaryEdges d (sctCutSites T)).filter (fun e => e.2 ∈ box d n)
  let i : Site d × Site d → Sym2 (sctBox d n) := fun e =>
    s(sctBoxize d n e.1, sctBoxize d n e.2)
  have hrestrict : sctInternalBoundaryCorr d beta n T =
      ∑ e ∈ C, sctEdgeBoundaryCorr beta T e := by
    unfold sctInternalBoundaryCorr C
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hc : sctCrossesCut T e
    · rw [if_pos hc]
    · rw [if_neg hc]
      induction e using Sym2.inductionOn with
      | _ x y =>
          unfold sctCrossesCut at hc
          simp only [Sym2.lift_mk] at hc
          by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;>
            simp [sctEdgeBoundaryCorr, hx, hy] at hc ⊢
  have hbij :
      (∑ e ∈ B, corrOriginInner d beta (sctCutSites T) e.1) =
        ∑ e ∈ C, sctEdgeBoundaryCorr beta T e := by
    apply Finset.sum_bij (fun e _ => i e)
    · intro e he
      have heB := Finset.mem_filter.mp he
      obtain ⟨_, _, h1S, h2S, _⟩ := boundaryEdges_outer heB.1
      have h1box := sctCutSites_subset_box T h1S
      have h2box := heB.2
      have hxT : sctBoxize d n e.1 ∈ T := by
        apply mem_sctCutSites.mp
        simpa [sctBoxize_val h1box] using h1S
      have hyT : sctBoxize d n e.2 ∉ T := by
        intro hy
        apply h2S
        have := mem_sctCutSites.mpr hy
        simpa [sctBoxize_val h2box] using this
      rw [Finset.mem_filter]
      constructor
      · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        simpa [sctBoxGraph, SimpleGraph.induce_adj, sctBoxize_val h1box,
          sctBoxize_val h2box] using boundaryEdges_adj heB.1
      · simp [sctCrossesCut, i, hxT, hyT]
    · intro a ha b hb hab
      have haB := (Finset.mem_filter.mp ha).1
      have hbB := (Finset.mem_filter.mp hb).1
      have ha2 := (Finset.mem_filter.mp ha).2
      have hb2 := (Finset.mem_filter.mp hb).2
      obtain ⟨_, _, ha1S, _, _⟩ := boundaryEdges_outer haB
      obtain ⟨_, _, hb1S, _, _⟩ := boundaryEdges_outer hbB
      have ha1box := sctCutSites_subset_box T ha1S
      have hb1box := sctCutSites_subset_box T hb1S
      have hamb : (s(a.1, a.2) : Sym2 (Site d)) = s(b.1, b.2) := by
        have hm := congrArg (Sym2.map (fun z : sctBox d n => z.1)) hab
        simpa [i, sctBoxize_val ha1box, sctBoxize_val ha2,
          sctBoxize_val hb1box, sctBoxize_val hb2] using hm
      exact boundaryEdges_sym2_injOn (sctCutSites T) haB hbB hamb
    · intro e he
      have heC := Finset.mem_filter.mp he
      induction e using Sym2.inductionOn with
      | _ x y =>
          have hadj : (sctBoxGraph d n).Adj x y := by
            simpa using SimpleGraph.mem_edgeFinset.mp heC.1
          have hlat : (hypercubicLattice d).Adj x.1 y.1 := by
            simpa [sctBoxGraph, SimpleGraph.induce_adj] using hadj
          have hcross := heC.2
          change (x ∈ T ∧ y ∉ T) ∨ (y ∈ T ∧ x ∉ T) at hcross
          rcases hcross with hxy | hyx
          · refine ⟨(x.1, y.1), ?_, ?_⟩
            · rw [Finset.mem_filter]
              exact ⟨mem_boundaryEdges_of_adj (sctCutSites T)
                (mem_sctCutSites.mpr hxy.1)
                (fun hy => hxy.2 (mem_sctCutSites.mp hy)) hlat, y.2⟩
            · have hxz : sctBoxize d n x.1 = x :=
                Subtype.ext (sctBoxize_val x.2)
              have hyz : sctBoxize d n y.1 = y :=
                Subtype.ext (sctBoxize_val y.2)
              simp [i, hxz, hyz]
          · refine ⟨(y.1, x.1), ?_, ?_⟩
            · rw [Finset.mem_filter]
              exact ⟨mem_boundaryEdges_of_adj (sctCutSites T)
                (mem_sctCutSites.mpr hyx.1)
                (fun hx => hyx.2 (mem_sctCutSites.mp hx)) hlat.symm, x.2⟩
            · have hxz : sctBoxize d n x.1 = x :=
                Subtype.ext (sctBoxize_val x.2)
              have hyz : sctBoxize d n y.1 = y :=
                Subtype.ext (sctBoxize_val y.2)
              simp [i, hxz, hyz, Sym2.eq_swap]
    · intro e he
      have heB := Finset.mem_filter.mp he
      obtain ⟨_, _, h1S, h2S, _⟩ := boundaryEdges_outer heB.1
      have h1box := sctCutSites_subset_box T h1S
      have h2box := heB.2
      have hxT : sctBoxize d n e.1 ∈ T := by
        apply mem_sctCutSites.mp
        simpa [sctBoxize_val h1box] using h1S
      have hyT : sctBoxize d n e.2 ∉ T := by
        intro hy
        apply h2S
        have := mem_sctCutSites.mpr hy
        simpa [sctBoxize_val h2box] using this
      simp [i, sctEdgeBoundaryCorr, hxT, hyT, sctBoxize_val h1box]
  rw [hrestrict, ← hbij]


end Sharpness
end StatMech
