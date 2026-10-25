/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentParity.Part2
open MeasureTheory Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Lattice StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem isingExpectation_spinProd_mono_graph
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (hGH : G ≤ H)
    (A : Finset V) :
    isingExpectation G beta h (spinProd A) ≤
      isingExpectation H beta h (spinProd A) := by
  rw [isingExpectation_spinProd_eq_expJ G,
    isingExpectation_spinProd_eq_expJ H]
  apply griffiths_mono G.edgeFinset H.edgeFinset
    (fun _ ↦ beta) (fun _ ↦ beta * h)
  · exact SimpleGraph.edgeFinset_mono hGH
  · exact fun _ _ ↦ hbeta
  · exact fun _ ↦ mul_nonneg hbeta hh
  · exact fun e he _ ↦ H.not_isDiag_of_mem_edgeFinset he

theorem isingExpectation_spinProd_induce_le
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (P : V → Prop) [DecidablePred P]
    (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (A : Finset {u // P u}) :
    isingExpectation (K.comap (Subtype.val : {u // P u} → V)) beta h
        (spinProd A) ≤
      isingExpectation K beta h
        (spinProd (A.map (Function.Embedding.subtype P))) := by
  let L : SimpleGraph {u // P u} := StatMech.FK.agl_left K P
  let R : SimpleGraph {u // ¬ P u} := StatMech.FK.agl_right K P
  let I : SimpleGraph {u // ¬ P u} := ⊥
  let S : SimpleGraph ({u // P u} ⊕ {u // ¬ P u}) := L ⊕g I
  let T : SimpleGraph ({u // P u} ⊕ {u // ¬ P u}) :=
    StatMech.FK.agl_glueGraph K P
  have hSI : S ≤ L ⊕g R := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · change L.Adj a b at hab ⊢
      exact hab
    · exfalso
      simpa only [S, SimpleGraph.sum_adj] using hab
    · exfalso
      simpa only [S, SimpleGraph.sum_adj] using hab
    · exfalso
      simpa only [S, I, SimpleGraph.sum_adj, SimpleGraph.bot_adj] using hab
  have hST : S ≤ T :=
    le_trans hSI (show L ⊕g R ≤ T from
      (StatMech.FK.agl_partitionCrossInterface K P).le)
  have hmap :
      (A.map ⟨Sum.inl, Sum.inl_injective⟩).map
          (StatMech.FK.agl_sumEquiv P).toEmbedding =
        A.map (Function.Embedding.subtype P) := by
    rw [Finset.map_map]
    apply congrArg (fun e : {u // P u} ↪ V ↦ A.map e)
    ext x
    rfl
  calc
    isingExpectation (K.comap (Subtype.val : {u // P u} → V)) beta h
        (spinProd A) =
        isingExpectation S beta h
          (spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩)) := by
      symm
      exact isingExpectation_spinProd_sum_inl L I beta h A
    _ ≤ isingExpectation T beta h
          (spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩)) :=
      isingExpectation_spinProd_mono_graph S T beta h hbeta hh hST _
    _ = isingExpectation K beta h
          (spinProd (A.map (Function.Embedding.subtype P))) := by
      rw [isingExpectation_spinProd_relabel T K
        (StatMech.FK.agl_sumEquiv P)
        (StatMech.FK.agl_glueGraph_adj K P) beta h
        (A.map ⟨Sum.inl, Sum.inl_injective⟩)]
      rw [hmap]

end StatMech.FrontierB
