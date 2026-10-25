/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
import Theorem.StatisticalMechanics.Code.Universality.Rot90Reindex
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWDualVCrossingClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
open Set SimpleGraph MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem rfr_rotbox_dichotomy_false : ¬ DualVerticalCrossing bcc_wallCfg (-2) 0 0 2 := by
  rintro ⟨x, y, hxy⟩
  have hx1 : (x : Site 2) 1 = 0 := x.2.2
  have hy1 : (y : Site 2) 1 = 2 := y.2.2
  obtain ⟨w⟩ := hxy
  have key : ∀ {a b : (rect (-2) 0 0 2 : Set (Site 2))},
      (openSubgraphInduce 2 (dualConfig bcc_wallCfg) (rect (-2) 0 0 2)).Walk a b →
      (a : Site 2) 1 ≤ 1 → (b : Site 2) 1 ≤ 1 := by
    intro a b ww
    induction ww with
    | nil => exact id
    | @cons p q r hpq _ ih =>
      intro hp
      rw [openSubgraphInduce_adj, openSubgraph_adj] at hpq
      exact ih (bcc_dualOpen_snd_le hpq.2).2
  have hstart : ((⟨(x : Site 2), bottomSide_subset x.2⟩ : (rect (-2) 0 0 2 : Set (Site 2)))
      : Site 2) 1 ≤ 1 := by rw [hx1]; norm_num
  have hend : (y : Site 2) 1 ≤ 1 := key w hstart
  rw [hy1] at hend; norm_num at hend


theorem rfr_negCut_open_snd_eq {u v : Site 2}
    (h : IsOpenEdge 2 (des_negConfig des_cutConfig) u v) : u 1 = v 1 := by
  obtain ⟨hadj, hopen⟩ := h
  rw [des_negConfig_open_iff_closed] at hopen
  by_contra hcon
  apply absurd hopen
  rw [des_cutConfig_open_of_not_cut]
  · simp
  · rintro ⟨c, hc⟩
    rw [Sym2.eq_iff] at hc
    rcases hc with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> (subst hu; subst hv; simp at hcon)


theorem rfr_negCut_connectedWithin_snd_eq {S : Set (Site 2)} {x y : S}
    (h : ConnectedWithin 2 (des_negConfig des_cutConfig) S x y) :
    (x : Site 2) 1 = (y : Site 2) 1 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | @cons a b c hab _ ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    exact (rfr_negCut_open_snd_eq hab).trans ih


theorem rfr_inplace_closedV_false (n : ℤ) (hn : 2 ≤ n) :
    ¬ VerticalCrossing (des_negConfig des_cutConfig) 0 n 0 n := by
  rintro ⟨x, y, hxy⟩
  have hsnd := rfr_negCut_connectedWithin_snd_eq hxy
  have hx1 : (x : Site 2) 1 = 0 := x.2.2
  have hy1 : (y : Site 2) 1 = n := y.2.2
  rw [hx1, hy1] at hsnd
  omega


theorem rfr_all_frames_fail :
    (¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ ¬ DualVerticalCrossing bcc_wallCfg 0 2 0 2) ∧
      (¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ ¬ DualVerticalCrossing bcc_wallCfg (-2) 0 0 2) ∧
      (¬ HorizontalCrossing des_cutConfig 0 2 0 2 ∧
        ¬ VerticalCrossing (des_negConfig des_cutConfig) 0 2 0 2) :=
  ⟨⟨bcc_noH_wall, bcc_noV_wall⟩,
   ⟨bcc_noH_wall, rfr_rotbox_dichotomy_false⟩,
   ⟨des_cutConfig_no_H 2 (by norm_num), rfr_inplace_closedV_false 2 (by norm_num)⟩⟩


theorem rfr_dualV_eq_negH_rotbox (n : ℤ) :
    dualVerticalCrossingEvent 0 n 0 n
      = {ω | HorizontalCrossing (des_negConfig ω) 0 n (-n) 0} :=
  des_dualVerticalCrossingEvent_eq n


theorem rfr_dualV_prob_eq (n : ℤ) (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n)) :
    rba_selfDualMeasure.real (dualVerticalCrossingEvent 0 n 0 n)
      = rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) :=
  rba_dualVerticalCrossing_eq 0 n 0 n hmeasV


theorem rfr_dual_measurePreserving :
    MeasurePreserving (dualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)))
      rba_selfDualMeasure rba_selfDualMeasure :=
  r90_dual_measurePreserving


end Universality
end StatMech
