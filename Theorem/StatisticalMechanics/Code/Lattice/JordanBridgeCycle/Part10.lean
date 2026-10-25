/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Def.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part9
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jbc_not_pushed_ym1 {a b : Site 2} (ha : a 1 = -1) :
    ¬ (jei_pushGraph jbc_Pce jbc_cyc4).Adj a b := by
  rintro ⟨i, _, _, hi, _⟩
  have : (jbc_csq i) 1 = -1 := by rw [show jbc_csq i = a from hi]; exact ha
  rcases jbc_csq_y i with h | h <;> rw [h] at this <;> omega

theorem jbc_not_pushed_ym1' {a b : Site 2} (hb : b 1 = -1) :
    ¬ (jei_pushGraph jbc_Pce jbc_cyc4).Adj a b :=
  fun h => jbc_not_pushed_ym1 hb h.symm

theorem jbc_latadj {a b : Site 2} (h : (∑ i, (a i - b i).natAbs) = 1) :
    (hypercubicLattice 2).Adj a b := by rw [hypercubicLattice_adj]; exact h


theorem jbc_around_reach :
    (jbc_latticeMinusEdges (jei_pushGraph jbc_Pce jbc_cyc4)).Reachable ![0, 0] ![1, 0] := by
  have step1 : (jbc_latticeMinusEdges (jei_pushGraph jbc_Pce jbc_cyc4)).Adj ![0, 0] ![0, -1] := by
    rw [jbc_latticeMinusEdges_adj]
    refine ⟨jbc_latadj (by rw [Fin.sum_univ_two]; norm_num), ?_⟩
    rw [SimpleGraph.mem_edgeSet]; exact jbc_not_pushed_ym1' (by norm_num [Matrix.cons_val_one])
  have step2 : (jbc_latticeMinusEdges (jei_pushGraph jbc_Pce jbc_cyc4)).Adj ![0, -1] ![1, -1] := by
    rw [jbc_latticeMinusEdges_adj]
    refine ⟨jbc_latadj (by rw [Fin.sum_univ_two]; norm_num), ?_⟩
    rw [SimpleGraph.mem_edgeSet]; exact jbc_not_pushed_ym1 (by norm_num [Matrix.cons_val_one])
  have step3 : (jbc_latticeMinusEdges (jei_pushGraph jbc_Pce jbc_cyc4)).Adj ![1, -1] ![1, 0] := by
    rw [jbc_latticeMinusEdges_adj]
    refine ⟨jbc_latadj (by rw [Fin.sum_univ_two]; norm_num), ?_⟩
    rw [SimpleGraph.mem_edgeSet]; exact jbc_not_pushed_ym1 (by norm_num [Matrix.cons_val_one])
  exact step1.reachable.trans (step2.reachable.trans step3.reachable)

theorem jbc_Pce_emb0 : jbc_Pce.emb jbc_v0 = ![0, 0] := rfl

theorem jbc_Pce_emb1 : jbc_Pce.emb jbc_v1 = ![1, 0] := rfl


theorem jbc_Pce_Gadj : jbc_Pce.G.Adj jbc_v0 jbc_v1 := by
  change jbc_cyc4.Adj jbc_v0 jbc_v1; rw [jbc_cyc4_adj]; decide

theorem jbc_Pce_not_Kadj : ¬ jbc_path3.Adj jbc_v0 jbc_v1 := by rw [jbc_path3_adj]; decide


theorem jbc_enlarged_reach :
    (jbc_latticeMinusEdges (jei_pushGraph jbc_Pce (jbc_path3 ⊔ edge jbc_v0 jbc_v1))).Reachable
      (jbc_Pce.emb jbc_v0) (jbc_Pce.emb jbc_v1) := by
  have hpush : jei_pushGraph jbc_Pce (jbc_path3 ⊔ edge jbc_v0 jbc_v1)
      = jei_pushGraph jbc_Pce jbc_cyc4 := congrArg _ jbc_path3_sup_edge
  rw [hpush, jbc_Pce_emb0, jbc_Pce_emb1]; exact jbc_around_reach

theorem jbc_jei_bridgeCycleDual_false : ¬ jei_BridgeCycleDual jbc_Pce := by
  intro hsync
  have hiff := hsync jbc_path3 jbc_path3_le_cyc4 jbc_Pce_Gadj jbc_Pce_not_Kadj
  have hDRiffR := jbc_dualSide_iff_primalAvoid jbc_Pce jbc_path3
    (x := jbc_v0) (y := jbc_v1) jbc_v0_ne_v1
  exact (hiff.mp jbc_path3_reach) (hDRiffR.mpr jbc_enlarged_reach)


theorem jbc_reducedBridgeCycle_false : ¬ jbc_ReducedBridgeCycle jbc_Pce :=
  fun h => jbc_jei_bridgeCycleDual_false (jbc_bridgeCycleDual_of_reduced jbc_Pce h)


theorem jbc_cycleDirection_false : ¬ jbc_CycleDirection jbc_Pce := by
  intro hcyc
  exact (hcyc jbc_path3 jbc_path3_le_cyc4 jbc_Pce_Gadj jbc_Pce_not_Kadj jbc_path3_reach)
    jbc_enlarged_reach


theorem jbc_crossSymm_pair (f g : Site 2) :
    crossEdge.symm s(f, g) = s(rot90Inv f, rot90Inv g) := by simp [crossEdge, sym2Congr]

theorem jbc_not_contour_ym1 {f g : Site 2} (h : (rot90Inv f) 1 = -1) :
    crossEdge.symm s(f, g) ∉ (jei_pushGraph jbc_Pce jbc_cyc4).edgeSet := by
  rw [jbc_crossSymm_pair, SimpleGraph.mem_edgeSet]
  rintro ⟨i, _, _, hi, _⟩
  have : (jbc_csq i) 1 = -1 := by rw [show jbc_csq i = rot90Inv f from hi]; exact h
  rcases jbc_csq_y i with hh | hh <;> rw [hh] at this <;> omega

theorem jbc_not_contour_ym1' {f g : Site 2} (h : (rot90Inv g) 1 = -1) :
    crossEdge.symm s(f, g) ∉ (jei_pushGraph jbc_Pce jbc_cyc4).edgeSet := by
  rw [Sym2.eq_swap]; exact jbc_not_contour_ym1 (f := g) (g := f) h

theorem jbc_vne {a b : Site 2} (h0 : a 0 ≠ b 0 ∨ a 1 ≠ b 1) : a ≠ b := by
  intro h; rcases h0 with hh | hh <;> [exact hh (by rw [h]); exact hh (by rw [h])]


theorem jbc_DR_true_direct :
    (regionGraph (jei_pushGraph jbc_Pce jbc_cyc4)).Reachable
      (rot90Fun (jbc_csq 0)) (rot90Fun (jbc_csq 1)) := by
  have e0 : rot90Fun (jbc_csq 0) = ![0, 0] := by simp [jbc_csq, rot90Fun]
  have e1 : rot90Fun (jbc_csq 1) = ![0, 1] := by simp [jbc_csq, rot90Fun]
  rw [e0, e1]
  have mkadj : ∀ f g : Site 2, (hypercubicLattice 2).Adj f g →
      crossEdge.symm s(f, g) ∉ (jei_pushGraph jbc_Pce jbc_cyc4).edgeSet →
      (regionGraph (jei_pushGraph jbc_Pce jbc_cyc4)).Adj f g := by
    intro f g hadj hpush; rw [regionGraph_adj]; exact ⟨hadj, hpush⟩
  have a1 : (regionGraph (jei_pushGraph jbc_Pce jbc_cyc4)).Adj ![0, 0] ![1, 0] :=
    mkadj _ _ (jbc_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (jbc_not_contour_ym1' (by rw [rot90Inv_apply]; norm_num [Matrix.cons_val_one]))
  have a2 : (regionGraph (jei_pushGraph jbc_Pce jbc_cyc4)).Adj ![1, 0] ![1, 1] :=
    mkadj _ _ (jbc_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (jbc_not_contour_ym1 (by rw [rot90Inv_apply]; norm_num [Matrix.cons_val_one]))
  have a3 : (regionGraph (jei_pushGraph jbc_Pce jbc_cyc4)).Adj ![1, 1] ![0, 1] :=
    mkadj _ _ (jbc_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (jbc_not_contour_ym1 (by rw [rot90Inv_apply]; norm_num [Matrix.cons_val_one]))
  exact a1.reachable.trans (a2.reachable.trans a3.reachable)


theorem jbc_jei_bridgeCycleDual_false_direct : ¬ jei_BridgeCycleDual jbc_Pce := by
  intro hsync
  have hiff := hsync jbc_path3 jbc_path3_le_cyc4 jbc_Pce_Gadj jbc_Pce_not_Kadj
  
  
  have hDR : ((regionGraph (jei_pushGraph jbc_Pce jbc_path3)).deleteEdges
      {crossEdge s(jbc_Pce.emb jbc_v0, jbc_Pce.emb jbc_v1)}).Reachable
      (rot90Fun (jbc_Pce.emb jbc_v0)) (rot90Fun (jbc_Pce.emb jbc_v1)) := by
    rw [jbc_deleteRegion_eq_pushSup jbc_Pce jbc_path3 jbc_v0_ne_v1]
    have hpush : jei_pushGraph jbc_Pce (jbc_path3 ⊔ edge jbc_v0 jbc_v1)
        = jei_pushGraph jbc_Pce jbc_cyc4 := congrArg _ jbc_path3_sup_edge
    rw [hpush, show jbc_Pce.emb jbc_v0 = jbc_csq 0 from rfl,
      show jbc_Pce.emb jbc_v1 = jbc_csq 1 from rfl]
    exact jbc_DR_true_direct
  exact (hiff.mp jbc_path3_reach) hDR

end Lattice
end StatMech
