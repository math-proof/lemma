/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDefectLowerStep_lift_reflTransGen
    {n D : Nat} {d e : Fin n → Nat}
    (h : Relation.ReflTransGen SixVertexDefectLowerStep d e)
    (hd : ∑ i, d i = D) :
    ∃ he : ∑ i, e i = D,
      Relation.ReflTransGen (sixVertexDefectLowerGraph n D).Adj
        ⟨d, hd⟩ ⟨e, he⟩ := by
  induction h with
  | refl => exact ⟨hd, Relation.ReflTransGen.refl⟩
  | @tail b c hab hbc ih =>
      obtain ⟨hb, hreach⟩ := ih
      have hc : ∑ i, c i = D := hbc.sum_eq.trans hb
      refine ⟨hc, hreach.tail ?_⟩
      exact Or.inl hbc


theorem sixVertexDefectLowerGraph_reachable_pile
    {n D : Nat} (hn : 0 < n) (d : SixVertexDefectState n D) :
    (sixVertexDefectLowerGraph n D).Reachable d
      ⟨sixVertexDefectPile hn D, sixVertexDefectPile_sum hn D⟩ := by
  have hfun := sixVertexDefectLowerStep_reaches_pile hn d.1
  obtain ⟨hpile, hlift⟩ :=
    sixVertexDefectLowerStep_lift_reflTransGen hfun d.2
  have hpileEq : sixVertexDefectPile hn (∑ i, d.1 i) =
      sixVertexDefectPile hn D := by rw [d.2]
  apply (SimpleGraph.reachable_iff_reflTransGen _ _).mpr
  simpa only [hpileEq, Subtype.mk.injEq] using hlift


theorem sixVertexDefectLowerGraph_preconnected
    {n D : Nat} (hn : 0 < n) :
    (sixVertexDefectLowerGraph n D).Preconnected := by
  intro d e
  exact (sixVertexDefectLowerGraph_reachable_pile hn d).trans
    (sixVertexDefectLowerGraph_reachable_pile hn e).symm


end
end StatMech.FrontierD
