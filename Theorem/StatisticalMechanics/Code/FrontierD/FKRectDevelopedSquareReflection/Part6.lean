/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectOpenEdgeCount_developedReflection
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration) :
    fkRectOpenEdgeCount R
        (fkRectDevelopedReflectionConfigurationEquiv R center omega) =
      fkRectOpenEdgeCount R omega := by
  unfold fkRectOpenEdgeCount
  let E := fkRectDevelopedReflectionEdgeEquiv R center
  apply Finset.card_bij (fun a _ => E.symm a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  · intro a ha b hb hab
    exact E.symm.injective hab
  · intro b hb
    refine ⟨E b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      change omega (E.symm (E b)) = true
      rw [E.symm_apply_apply]
      exact hb
    · exact E.symm_apply_apply b


theorem fkRectNumClusters_developedReflection
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration) :
    fkRectNumClusters R
        (fkRectDevelopedReflectionConfigurationEquiv R center omega) =
      fkRectNumClusters R omega := by
  unfold fkRectNumClusters
  exact (Fintype.card_congr
    (fkRectOpenGraphDevelopedReflectionIso R center omega).connectedComponentEquiv).symm


theorem fkRectCriticalReducedWeight_developedReflection
    (R : FKRectTorus) (center : Nat) (q : Real)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q
        (fkRectDevelopedReflectionConfigurationEquiv R center omega) =
      fkRectCriticalReducedWeight R q omega := by
  unfold fkRectCriticalReducedWeight
  rw [fkRectOpenEdgeCount_developedReflection,
    fkRectNumClusters_developedReflection]


theorem fkRectCriticalRandomClusterProb_developedReflection
    (R : FKRectTorus) (center : Nat) (q : Real)
    (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q
        (fkRectDevelopedReflectionConfigurationEquiv R center omega) =
      fkRectCriticalRandomClusterProb R q omega := by
  unfold fkRectCriticalRandomClusterProb
  rw [fkRectCriticalReducedWeight_developedReflection]


theorem fkRectFullGraphConfiguration_developedReflection
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration)
    (e : Sym2 R.Vertex) :
    fkRectFullGraphConfiguration R
        (fkRectDevelopedReflectionConfigurationEquiv R center omega)
        (Sym2.map (fkRectDevelopedReflectionVertexEquiv R center) e) =
      fkRectFullGraphConfiguration R omega e := by
  classical
  by_cases he : e ∈ (fkRectTorusGraph R).edgeSet
  · obtain ⟨a, ha⟩ := (mem_fkRectTorusGraph_edgeSet_iff R e).1 he
    rw [← ha, ← fkRectTorusIndexedEdge_developedReflection,
      fkRectFullGraphConfiguration_indexedEdge,
      fkRectFullGraphConfiguration_indexedEdge]
    change omega ((fkRectDevelopedReflectionEdgeEquiv R center).symm
      (fkRectDevelopedReflectionEdgeEquiv R center a)) = omega a
    rw [(fkRectDevelopedReflectionEdgeEquiv R center).symm_apply_apply]
  · have href : Sym2.map (fkRectDevelopedReflectionVertexEquiv R center) e ∉
        (fkRectTorusGraph R).edgeSet := by
      intro href
      induction e using Sym2.ind with
      | _ x y =>
        simp only [Sym2.map_mk] at href
        rw [SimpleGraph.mem_edgeSet] at href
        apply he
        rw [SimpleGraph.mem_edgeSet]
        exact (fkRectTorusGraph_adj_developedReflection
          R center x y).mp href
    rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R _ href,
      fkRectFullGraphConfiguration_eq_false_of_not_edge R _ he]


theorem fkRectDevelopedSquarePullback_developedReflection
    (R : FKRectTorus) (n : Nat) (omega : R.Configuration) :
    fkRectDevelopedSquarePullback R n
        (fkRectDevelopedReflectionConfigurationEquiv R n omega) =
      StatMech.Universality.crf_swapConfig
        (fkRectDevelopedSquarePullback R n omega) := by
  funext e
  induction e using Sym2.ind with
  | _ x y =>
    rw [StatMech.Universality.crf_swapConfig_apply]
    change fkRectFullGraphConfiguration R
        (fkRectDevelopedReflectionConfigurationEquiv R n omega)
          (Sym2.map (fkRectDevelopedSquareVertex R n) s(x, y)) =
      fkRectFullGraphConfiguration R omega
        (Sym2.map (fkRectDevelopedSquareVertex R n)
          (Sym2.map StatMech.Universality.crf_swap s(x, y)))
    rw [← fkRectFullGraphConfiguration_developedReflection R n omega
      (Sym2.map (fkRectDevelopedSquareVertex R n)
        (Sym2.map StatMech.Universality.crf_swap s(x, y)))]
    simp only [Sym2.map_mk]
    rw [fkRectDevelopedReflectionVertex_developedSquareVertex,
      fkRectDevelopedReflectionVertex_developedSquareVertex]
    simp only [StatMech.Universality.crf_swap_involutive]


theorem fkRectDevelopedSquare_reflection_mem_vertical_iff
    (R : FKRectTorus) (n : Nat) (omega : R.Configuration) :
    fkRectDevelopedReflectionConfigurationEquiv R n omega ∈
        fkRectDevelopedSquareVerticalCrossingEvent R n ↔
      omega ∈ fkRectDevelopedSquareHorizontalCrossingEvent R n := by
  rw [fkRectDevelopedSquareVerticalCrossingEvent,
    fkRectDevelopedSquareHorizontalCrossingEvent]
  change StatMech.RSW.Box.VerticalCrossing
      (fkRectDevelopedSquarePullback R n
        (fkRectDevelopedReflectionConfigurationEquiv R n omega)) 0 n 0 n ↔
    StatMech.RSW.Box.HorizontalCrossing
      (fkRectDevelopedSquarePullback R n omega) 0 n 0 n
  rw [fkRectDevelopedSquarePullback_developedReflection]
  constructor
  · intro hV
    have hH := StatMech.Universality.crf_vertical_to_horizontal
      0 n 0 n
      (StatMech.Universality.crf_swapConfig
        (fkRectDevelopedSquarePullback R n omega)) hV
    rwa [StatMech.Universality.bat_swapConfig_involutive] at hH
  · intro hH
    exact StatMech.Universality.bat_horizontal_to_vertical_swap
      0 n 0 n (fkRectDevelopedSquarePullback R n omega) hH


theorem fkRectCritical_developedSquareHorizontalMass_eq_verticalMass
    (R : FKRectTorus) (n : Nat) (q : Real) :
    fkRectCriticalEventMass R q
        (fkRectDevelopedSquareHorizontalCrossingEvent R n) =
      fkRectCriticalEventMass R q
        (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
  classical
  let C := fkRectDevelopedReflectionConfigurationEquiv R n
  let H := fkRectDevelopedSquareHorizontalCrossingEvent R n
  let V := fkRectDevelopedSquareVerticalCrossingEvent R n
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta : R.Configuration =>
    V.indicator (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega homega
  have hmem : C omega ∈ V ↔ omega ∈ H :=
    fkRectDevelopedSquare_reflection_mem_vertical_iff R n omega
  have hprob : fkRectCriticalRandomClusterProb R q (C omega) =
      fkRectCriticalRandomClusterProb R q omega :=
    fkRectCriticalRandomClusterProb_developedReflection R n q omega
  by_cases hH : omega ∈ H
  · rw [Set.indicator_of_mem hH, Set.indicator_of_mem (hmem.mpr hH), hprob]
  · rw [Set.indicator_of_notMem hH,
      Set.indicator_of_notMem (fun hV => hH (hmem.mp hV))]


theorem fkRectCritical_developedSquareHorizontalMass_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 <= n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 <= q) :
    1 / (2 * (1 + q)) <= fkRectCriticalEventMass R q
      (fkRectDevelopedSquareHorizontalCrossingEvent R n) := by
  rcases fkRectDevelopedSquare_exists_direction_crossing_ge
      R n hn hwidth hheight hq with hH | hV
  · exact hH
  · rwa [fkRectCritical_developedSquareHorizontalMass_eq_verticalMass]


theorem fkRectCritical_developedSquareVerticalMass_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 <= n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 <= q) :
    1 / (2 * (1 + q)) <= fkRectCriticalEventMass R q
      (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
  rw [← fkRectCritical_developedSquareHorizontalMass_eq_verticalMass]
  exact fkRectCritical_developedSquareHorizontalMass_ge
    R n hn hwidth hheight hq


theorem fkRectCritical_developedThreeByOneVerticalMass_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 <= n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 <= q) :
    1 / (2 * (1 + q)) <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleVerticalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n) := by
  exact (fkRectCritical_developedSquareVerticalMass_ge
    R n hn hwidth hheight hq).trans
      (fkRectCritical_developedSquareVerticalMass_le_threeByOneVerticalMass
        R n (zero_lt_one.trans_le hq))

end
end StatMech.FrontierD
