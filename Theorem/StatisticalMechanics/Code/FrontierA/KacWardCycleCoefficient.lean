/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
import Def.StatisticalMechanics.Code.FrontierA.KacWardCycleCoefficient
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager

universe u


theorem kwGraph_mem_squarefreeLoopFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    (loop : Fin n → G.Dart) :
    loop ∈ kwGraphSquarefreeLoopFinset G phase S ↔
      kwGraphLoopExponent G loop = ons_finsetExponent S ∧
        kwGraphLoopScalar G phase loop ≠ 0 := by
  simp [kwGraphSquarefreeLoopFinset]


theorem kwGraphLoopWalk_snd
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hvalid : ∀ k, G.DartAdj (loop k) (loop (k + 1))) :
    (kwGraphLoopWalk G loop hvalid).snd = (loop 0).snd := by
  have hdarts := kwGraphLoopWalk_darts G loop hvalid
  have hne : ¬(kwGraphLoopWalk G loop hvalid).Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    rw [← SimpleGraph.Walk.length_darts, hdarts, List.length_ofFn]
    exact NeZero.pos n
  have hpos : 0 < (kwGraphLoopWalk G loop hvalid).darts.length := by
    rw [hdarts, List.length_ofFn]
    exact NeZero.pos n
  have hfirst := SimpleGraph.Walk.firstDart_eq hne hpos
  have hfirst' : (kwGraphLoopWalk G loop hvalid).firstDart hne = loop 0 := by
    simpa only [kwGraphLoopWalk_darts, List.getElem_ofFn] using hfirst
  simpa using congrArg (fun dart : G.Dart ↦ dart.snd) hfirst'


theorem kwGraph_squarefreeLoop_eval_zero_injective
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V)) :
    Set.InjOn (fun loop : Fin n → G.Dart ↦ loop 0)
      (kwGraphSquarefreeLoopFinset (n := n) G phase S :
        Set (Fin n → G.Dart)) := by
  intro d hd e he hzero
  change d ∈ kwGraphSquarefreeLoopFinset G phase S at hd
  change e ∈ kwGraphSquarefreeLoopFinset G phase S at he
  rw [kwGraph_mem_squarefreeLoopFinset] at hd he
  let hdvalid := kwGraphLoop_valid_of_scalar_ne_zero G phase d hd.2
  let hevalid := kwGraphLoop_valid_of_scalar_ne_zero G phase e he.2
  let pd := kwGraphLoopWalk G d hdvalid
  let pe := kwGraphLoopWalk G e hevalid
  have hdtrail := kwGraphLoopWalk_isTrail_and_edges G d hdvalid S hd.1
  have hetrail := kwGraphLoopWalk_isTrail_and_edges G e hevalid S he.1
  have hpdne : pd ≠ .nil := by
    intro hnil
    have hlen := congrArg List.length (kwGraphLoopWalk_darts G d hdvalid)
    rw [show kwGraphLoopWalk G d hdvalid = pd from rfl, hnil] at hlen
    simp at hlen
    exact (NeZero.ne n) hlen.symm
  have hpene : pe ≠ .nil := by
    intro hnil
    have hlen := congrArg List.length (kwGraphLoopWalk_darts G e hevalid)
    rw [show kwGraphLoopWalk G e hevalid = pe from rfl, hnil] at hlen
    simp at hlen
    exact (NeZero.ne n) hlen.symm
  have hpd : pd.IsCycle :=
    kw_closedTrail_isCycle_of_degree_le_three G pd hdtrail.1 hpdne hdeg
  have hpe : pe.IsCycle :=
    kw_closedTrail_isCycle_of_degree_le_three G pe hetrail.1 hpene hdeg
  let pe' : G.Walk (d 0).fst (d 0).fst := pe.copy
    (congrArg (fun dart : G.Dart ↦ dart.fst) hzero).symm
    (congrArg (fun dart : G.Dart ↦ dart.fst) hzero).symm
  have hpe' : pe'.IsCycle := by
    exact (SimpleGraph.Walk.isCycle_copy pe
      (congrArg (fun dart : G.Dart ↦ dart.fst) hzero).symm).mpr hpe
  have hsnd : pd.snd = pe'.snd := by
    rw [kwGraphLoopWalk_snd G d hdvalid]
    change (d 0).snd = (pe.copy _ _).snd
    change (d 0).snd = (pe.copy _ _).getVert 1
    rw [SimpleGraph.Walk.getVert_copy]
    change (d 0).snd = pe.snd
    rw [kwGraphLoopWalk_snd G e hevalid]
    exact congrArg (fun dart : G.Dart ↦ dart.snd) hzero
  have hedges : pd.edges.toFinset = pe'.edges.toFinset := by
    rw [show pd.edges.toFinset = S from hdtrail.2,
      SimpleGraph.Walk.edges_copy]
    exact hetrail.2.symm
  have hpde : pd = pe' :=
    ons_rooted_isCycle_eq_of_snd_edges_eq pd pe' hpd hpe' hsnd hedges
  apply List.ofFn_injective
  rw [← kwGraphLoopWalk_darts G d hdvalid,
    ← kwGraphLoopWalk_darts G e hevalid]
  simpa [pd, pe, pe'] using congrArg SimpleGraph.Walk.darts hpde

theorem kwGraphLoopExponent_rotate
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) (r : Fin n) :
    kwGraphLoopExponent G (ons_rotate r loop) =
      kwGraphLoopExponent G loop := by
  unfold kwGraphLoopExponent
  simpa [ons_rotate, add_comm, add_left_comm, add_assoc] using
    Equiv.sum_comp (Equiv.addRight r)
      (fun k : Fin n ↦ Finsupp.single (loop k).edge 1)

theorem kwGraphLoopScalar_rotate
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) (r : Fin n) :
    kwGraphLoopScalar G phase (ons_rotate r loop) =
      kwGraphLoopScalar G phase loop := by
  exact ons_loopWeight_rotate
    (kwGraphTransition G (fun _ ↦ 1) phase) r loop


end StatMech.FrontierA
