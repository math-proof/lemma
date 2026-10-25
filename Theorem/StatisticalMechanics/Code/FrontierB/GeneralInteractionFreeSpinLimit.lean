/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSpinLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousFiniteVolumeRelabel.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeSpinLimit
open Filter Topology Set
open scoped BigOperators
open Finset


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Sharpness StatMech.Lattice


@[simp] theorem interactionBoxPredEquiv_val (d : Nat) {n m : Nat}
    (hnm : n ≤ m) (x : interactionBoxVertices d n) :
    (interactionBoxPredEquiv d hnm x).1.1 = x.1 := rfl

theorem interactionBoxGraph_edge_nonDiag (d n : Nat)
    (e : Sym2 (interactionBoxVertices d n))
    (he : e ∈ (interactionBoxGraph d n).edgeFinset) : ¬e.IsDiag := by
  exact (interactionBoxGraph d n).not_isDiag_of_mem_edgeFinset he

theorem interactionBox_induced_edges_subset (d : Nat) {n m : Nat}
    (hnm : n ≤ m) :
    sym2FinsetImage
        (StatMech.FK.agl_sumEquiv
          (fun x : interactionBoxVertices d m => x.1 ∈ box d n))
        (sym2FinsetInl
          (sym2FinsetImage (interactionBoxPredEquiv d hnm)
            (interactionBoxGraph d n).edgeFinset) :
          Finset (Sym2
            ({x : interactionBoxVertices d m // x.1 ∈ box d n} ⊕
             {x : interactionBoxVertices d m // x.1 ∉ box d n}))) ⊆
      (interactionBoxGraph d m).edgeFinset := by
  intro e he
  unfold sym2FinsetImage sym2FinsetInl at he
  simp only [Finset.mem_image] at he
  obtain ⟨eSum, heSum, rfl⟩ := he
  obtain ⟨ePred, hePred, rfl⟩ := heSum
  obtain ⟨eSmall, heSmall, rfl⟩ := hePred
  have hnonDiag : ¬(Sym2.map
      (StatMech.FK.agl_sumEquiv
        (fun x : interactionBoxVertices d m => x.1 ∈ box d n))
      (Sym2.map Sum.inl
        (Sym2.map (interactionBoxPredEquiv d hnm) eSmall))).IsDiag := by
    rw [Sym2.isDiag_map
      (StatMech.FK.agl_sumEquiv
        (fun x : interactionBoxVertices d m => x.1 ∈ box d n)).injective]
    rw [Sym2.isDiag_map Sum.inl_injective]
    rw [Sym2.isDiag_map (interactionBoxPredEquiv d hnm).injective]
    exact interactionBoxGraph_edge_nonDiag d n eSmall heSmall
  rw [SimpleGraph.mem_edgeFinset]
  simpa [interactionBoxGraph] using hnonDiag


theorem generalInteractionBox_spinProd_mono {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 ≤ beta) {n m : Nat} (hnm : n ≤ m)
    (A : Finset (interactionBoxVertices d n)) :
    expJ (interactionBoxGraph d n).edgeFinset
        (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0)
        (spinProd A) ≤
      expJ (interactionBoxGraph d m).edgeFinset
        (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0)
        (spinProd (A.map (interactionBoxVertexIncl d hnm))) := by
  let P : interactionBoxVertices d m → Prop :=
    fun x => x.1 ∈ box d n
  let sigma : interactionBoxVertices d n ≃ {x // P x} :=
    interactionBoxPredEquiv d hnm
  let E : Finset (Sym2 {x // P x}) :=
    sym2FinsetImage sigma (interactionBoxGraph d n).edgeFinset
  let Jm : Sym2 (interactionBoxVertices d m) → ℝ :=
    fun e => beta * interactionBoxCoupling J m e
  let AP : Finset {x // P x} := A.map sigma.toEmbedding
  have hsmall :
      expJ (interactionBoxGraph d n).edgeFinset
          (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0)
          (spinProd A) =
        expJ E (fun e => Jm (Sym2.map Subtype.val e)) (fun _ => 0)
          (spinProd AP) := by
    have hcouple :
        (fun e => beta * interactionBoxCoupling J n e) =
          (fun e => Jm (Sym2.map Subtype.val (Sym2.map sigma e))) := by
      funext e
      induction e using Sym2.inductionOn with
      | _ x y =>
          simp [Jm, interactionBoxCoupling, sigma,
            interactionBoxPredEquiv]
    rw [hcouple]
    exact expJ_spinProd_sym2FinsetImage_relabel sigma
      (interactionBoxGraph d n).edgeFinset
      (fun e => Jm (Sym2.map Subtype.val e)) (fun _ => 0) A
  rw [hsmall]
  have hmono := expJ_spinProd_induce_le P E
    (interactionBoxGraph d m).edgeFinset Jm
    (by
      simpa only [P, E, sigma] using
        interactionBox_induced_edges_subset d hnm)
    (by
      intro e he
      exact mul_nonneg hbeta (hJ (Sym2.map Subtype.val e)))
    (fun e he => (interactionBoxGraph d m).not_isDiag_of_mem_edgeFinset he)
    AP
  have hsupport :
      AP.map (Function.Embedding.subtype P) =
        A.map (interactionBoxVertexIncl d hnm) := by
    rw [Finset.map_map]
    apply congrArg (fun f : interactionBoxVertices d n ↪
      interactionBoxVertices d m => A.map f)
    apply Function.Embedding.ext
    intro x
    apply Subtype.ext
    rfl
  simpa only [Jm, P, E, AP, hsupport] using hmono


end StatMech.FrontierB
