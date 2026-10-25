/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitEmbedding.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePrimitive.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitPhase.Part3


namespace StatMech.FrontierA

open SimpleGraph


theorem triangularTorusSplitPhaseGauge_ne_zero
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart) :
    triangularTorusSplitPhaseGauge L rho d ≠ 0 := by
  unfold triangularTorusSplitPhaseGauge
  split
  · norm_num
  · unfold triangularTorusSplitInternalGauge
    split <;> exact pow_ne_zero _ (triangularTorusTurnRoot_ne_zero rho hrho)

theorem triangularTorusSplit_embedPhase_eq_phaseGauge
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (d e : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart)
    (hconnect : d.snd = e.fst) (hne : d.edge ≠ e.edge) :
    triangularTorusGraphPhase (3 * L) rho 1 1
        ((triangularTorusSplitEmbedHom L).mapDart d)
        ((triangularTorusSplitEmbedHom L).mapDart e) =
      kwPhaseGauge (triangularTorusSplitPhaseGauge L rho)
        (kwLocalAngularSplitPhase
          (triangularTorusLocalAngularData L rho hrho)) d e := by
  classical
  rw [triangularTorusGraphPhase_one_one_apply,
    triangularTorusSplitEmbedHom_mapDart_direction,
    triangularTorusSplitEmbedHom_mapDart_direction]
  unfold kwPhaseGauge
  by_cases hd : kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm
  · by_cases he : kwDartOfPort (triangularTorusGraph L) e.snd =
        (kwDartOfPort (triangularTorusGraph L) e.fst).symm
    · exfalso
      apply hne
      have hsnd : e.snd = d.fst := by
        apply kwDartOfPort_injective (triangularTorusGraph L)
        rw [he, ← hconnect, hd]
        simp
      have hedart : e = d.symm := by
        apply SimpleGraph.Dart.ext
        exact Prod.ext hconnect.symm hsnd
      rw [hedart]
      exact d.edge_symm.symm
    · have einfo := (kwOrderedDartPortSplitGraph_adj
          (triangularTorusGraph L) (triangularTorusLocalPortOrder L)
          e.fst e.snd).mp e.adj |>.resolve_left he
      generalize ha : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) e.fst) = a
      generalize hb : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) e.snd) = b
      have hadj : (triangularTorusDirectionRank a).val + 1 =
            (triangularTorusDirectionRank b).val ∨
          (triangularTorusDirectionRank b).val + 1 =
            (triangularTorusDirectionRank a).val := by
        simpa [triangularTorusLocalPortOrder_rank, ha, hb] using einfo.2
      have hdir : triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) d.fst) =
          triangularTorusDirectionReverse a := by
        have harev : a = triangularTorusDirectionReverse
            (triangularTorusGraphDartDirection L
              (kwDartOfPort (triangularTorusGraph L) d.fst)) := by
          calc
            a = triangularTorusGraphDartDirection L
                (kwDartOfPort (triangularTorusGraph L) e.fst) := ha.symm
            _ = triangularTorusGraphDartDirection L
                (kwDartOfPort (triangularTorusGraph L) d.snd) := by
              rw [hconnect]
            _ = triangularTorusGraphDartDirection L
                (kwDartOfPort (triangularTorusGraph L) d.fst).symm := by
              rw [hd]
            _ = triangularTorusDirectionReverse
                (triangularTorusGraphDartDirection L
                  (kwDartOfPort (triangularTorusGraph L) d.fst)) :=
              triangularTorusGraphDartDirection_symm L _
        let z := triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) d.fst)
        calc
          z = triangularTorusDirectionReverse
              (triangularTorusDirectionReverse z) := by
            exact (triangularOppositeDirection_reverse z).symm
          _ = triangularTorusDirectionReverse a :=
            (congrArg triangularTorusDirectionReverse harev).symm
      simpa [triangularTorusSplitDartDirection,
        triangularTorusSplitPhaseGauge, kwLocalAngularSplitPhase,
        triangularTorusLocalAngularData, triangularTorusLocalPortRoot,
        triangularTorusLocalPortOrder_rank,
        hd, he, ha, hb, hdir] using
        (triangularSplit_entry_phase rho hrho a b hadj)
  · by_cases he : kwDartOfPort (triangularTorusGraph L) e.snd =
        (kwDartOfPort (triangularTorusGraph L) e.fst).symm
    · have dinfo := (kwOrderedDartPortSplitGraph_adj
          (triangularTorusGraph L) (triangularTorusLocalPortOrder L)
          d.fst d.snd).mp d.adj |>.resolve_left hd
      generalize ha : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.fst) = a
      generalize hb : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.snd) = b
      have hadj : (triangularTorusDirectionRank a).val + 1 =
            (triangularTorusDirectionRank b).val ∨
          (triangularTorusDirectionRank b).val + 1 =
            (triangularTorusDirectionRank a).val := by
        simpa [triangularTorusLocalPortOrder_rank, ha, hb] using dinfo.2
      have hedir : triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) e.fst) = b := by
        rw [← hconnect, hb]
      simpa [triangularTorusSplitDartDirection,
        triangularTorusSplitPhaseGauge, kwLocalAngularSplitPhase,
        triangularTorusLocalAngularData, triangularTorusLocalPortRoot,
        hd, he, ha, hb, hedir] using
        (triangularSplit_exit_phase rho hrho a b hadj)
    · let di : KWOrderedInternalSplitDart (triangularTorusGraph L)
          (triangularTorusLocalPortOrder L) := ⟨d, hd⟩
      let ei : KWOrderedInternalSplitDart (triangularTorusGraph L)
          (triangularTorusLocalPortOrder L) := ⟨e, he⟩
      have hstep : KWOrderedInternalDartStep (triangularTorusGraph L)
          (triangularTorusLocalPortOrder L) di ei := ⟨hconnect, hne⟩
      have dinfo := kwOrderedInternalSplitDart_adj_data
        (triangularTorusGraph L) (triangularTorusLocalPortOrder L) di
      have einfo := kwOrderedInternalSplitDart_adj_data
        (triangularTorusGraph L) (triangularTorusLocalPortOrder L) ei
      generalize ha : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.fst) = a
      generalize hb : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.snd) = b
      generalize hc : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) e.snd) = c
      have hefst : triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) e.fst) = b := by
        rw [← hconnect, hb]
      have hab : (triangularTorusDirectionRank a).val + 1 =
            (triangularTorusDirectionRank b).val ∨
          (triangularTorusDirectionRank b).val + 1 =
            (triangularTorusDirectionRank a).val := by
        simpa [di, triangularTorusLocalPortOrder_rank, ha, hb] using dinfo.2
      have hbc : (triangularTorusDirectionRank b).val + 1 =
            (triangularTorusDirectionRank c).val ∨
          (triangularTorusDirectionRank c).val + 1 =
            (triangularTorusDirectionRank b).val := by
        simpa [ei, triangularTorusLocalPortOrder_rank, hefst, hc] using einfo.2
      have hmono : ((triangularTorusDirectionRank a).val <
            (triangularTorusDirectionRank b).val ∧
          (triangularTorusDirectionRank b).val <
            (triangularTorusDirectionRank c).val) ∨
        ((triangularTorusDirectionRank b).val <
            (triangularTorusDirectionRank a).val ∧
          (triangularTorusDirectionRank c).val <
            (triangularTorusDirectionRank b).val) := by
        by_cases hinc : kwOrderedPortRank (triangularTorusLocalPortOrder L)
            d.fst < kwOrderedPortRank (triangularTorusLocalPortOrder L) d.snd
        · left
          refine ⟨?_, ?_⟩
          · simpa [triangularTorusLocalPortOrder_rank, ha, hb] using hinc
          · have heinc := kwOrderedInternalDartStep_rank_lt
              (triangularTorusGraph L) (triangularTorusLocalPortOrder L)
              hstep hinc
            simpa [di, ei, triangularTorusLocalPortOrder_rank,
              hefst, hc] using heinc
        · right
          have hdec : kwOrderedPortRank (triangularTorusLocalPortOrder L)
              d.snd < kwOrderedPortRank (triangularTorusLocalPortOrder L)
                d.fst := by
            have dranks :
                kwOrderedPortRank (triangularTorusLocalPortOrder L) d.fst + 1 =
                    kwOrderedPortRank (triangularTorusLocalPortOrder L) d.snd ∨
                  kwOrderedPortRank (triangularTorusLocalPortOrder L) d.snd + 1 =
                    kwOrderedPortRank (triangularTorusLocalPortOrder L) d.fst := by
              simpa [di] using dinfo.2
            rcases dranks with h | h <;> omega
          refine ⟨?_, ?_⟩
          · simpa [triangularTorusLocalPortOrder_rank, ha, hb] using hdec
          · have hedec := kwOrderedInternalDartStep_rank_gt
              (triangularTorusGraph L) (triangularTorusLocalPortOrder L)
              hstep hdec
            simpa [di, ei, triangularTorusLocalPortOrder_rank,
              hefst, hc] using hedec
      simpa [triangularTorusSplitDartDirection,
        triangularTorusSplitPhaseGauge, kwLocalAngularSplitPhase,
        triangularTorusLocalAngularData, hd, he, ha, hb, hefst, hc] using
        (triangularSplit_internal_phase rho hrho a b c hab hbc hmono)

end StatMech.FrontierA
