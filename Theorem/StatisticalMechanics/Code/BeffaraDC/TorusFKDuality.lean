/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusGeometricEuler.Part3
import Def.StatisticalMechanics.Code.BeffaraDC.TorusFKDuality
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


theorem torusQuarterTurnEdge_mem_edgeFinset (L : ℕ) [Fact (2 < L)]
    (e : Sym2 (ZMod L × ZMod L)) :
    e ∈ (onsTorusGraph L).edgeFinset ↔
      torusQuarterTurnEdge L e ∈ (onsTorusGraph L).edgeFinset := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [SimpleGraph.mem_edgeFinset, torusQuarterTurnEdge,
        Equiv.coe_fn_mk, Sym2.map_mk]
      exact (torusQuarterTurn_adj_iff L x y).symm


theorem torus_dual_openCount (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.openCount (onsTorusGraph L) (torusDualConfig L ω) =
      (onsTorusGraph L).edgeFinset.card - FK.openCount (onsTorusGraph L) ω := by
  classical
  unfold FK.openCount
  have hopen : (onsTorusGraph L).edgeFinset.filter
      (fun e => torusDualConfig L ω e = true) =
      (onsTorusGraph L).edgeFinset.filter
        (fun e => ω (torusQuarterTurnEdge L e) = false) := by
    ext e
    simp only [Finset.mem_filter, torusDualConfig, torusQuarterTurnEdge,
      Equiv.coe_fn_mk]
    cases h : ω (Sym2.map (torusQuarterTurn L) e) <;> simp
  rw [hopen, show ((onsTorusGraph L).edgeFinset.filter
      (fun e => ω (torusQuarterTurnEdge L e) = false)).card =
      ((onsTorusGraph L).edgeFinset.filter (fun e => ω e = false)).card from by
    apply Finset.card_bij (fun e _ => torusQuarterTurnEdge L e)
    · intro e he
      simp only [Finset.mem_filter] at he ⊢
      exact ⟨(torusQuarterTurnEdge_mem_edgeFinset L e).mp he.1, he.2⟩
    · intro a ha b hb hab
      exact (torusQuarterTurnEdge L).injective hab
    · intro b hb
      refine ⟨(torusQuarterTurnEdge L).symm b, ?_,
        (torusQuarterTurnEdge L).apply_symm_apply b⟩
      simp only [Finset.mem_filter] at hb ⊢
      exact ⟨(torusQuarterTurnEdge_mem_edgeFinset L
        ((torusQuarterTurnEdge L).symm b)).mpr (by simpa using hb.1), by simpa using hb.2⟩]
  have hc := Finset.card_filter_add_card_filter_not
    (s := (onsTorusGraph L).edgeFinset) (fun e => ω e = true)
  have hnot : (onsTorusGraph L).edgeFinset.filter (fun e => ¬ω e = true) =
      (onsTorusGraph L).edgeFinset.filter (fun e => ω e = false) := by
    ext e
    simp only [Finset.mem_filter]
    cases ω e <;> simp
  rw [hnot] at hc
  omega


theorem torus_openSub_dualConfig (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.openSub (onsTorusGraph L) (torusDualConfig L ω) =
      torusDualCutGraph L (FK.openSub (onsTorusGraph L) ω) := by
  ext f g
  simp only [FK.openSub_adj, torusDualCutGraph_adj, torusDualConfig, Sym2.map_mk]
  rw [torusQuarterTurn_adj_iff]
  by_cases h : (onsTorusGraph L).Adj f g <;> simp [h]


theorem torus_numClusters_dualConfig (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.numClusters (onsTorusGraph L) (torusDualConfig L ω) =
      torusGeometricFaceCount L (FK.openSub (onsTorusGraph L) ω) := by
  unfold FK.numClusters torusGeometricFaceCount
  rw [← Nat.card_eq_fintype_card]
  exact congrArg (fun G : SimpleGraph (ZMod L × ZMod L) =>
    Nat.card G.ConnectedComponent) (torus_openSub_dualConfig L ω)


end StatMech.BeffaraDC
