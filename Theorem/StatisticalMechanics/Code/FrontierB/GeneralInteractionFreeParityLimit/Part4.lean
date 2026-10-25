/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeSpinLimit.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousParityAvoidance.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity.Part3
import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeParityLimit.Part4
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Ising Lattice

theorem interactionBoxTransportedEdges_subset_edgeFinset (d : Nat)
    {n m : Nat} (hnm : n ≤ m)
    (E : Finset (Sym2 (interactionBoxVertices d n)))
    (hE : E ⊆ (interactionBoxGraph d n).edgeFinset) :
    interactionBoxTransportedEdges d hnm E ⊆
      (interactionBoxGraph d m).edgeFinset := by
  intro e he
  unfold interactionBoxTransportedEdges sym2FinsetMap at he
  rw [Finset.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [SimpleGraph.mem_edgeFinset]
  have hnonDiag : ¬f.IsDiag :=
    (interactionBoxGraph d n).not_isDiag_of_mem_edgeFinset (hE hf)
  have hmapped : ¬(Sym2.map (interactionBoxVertexIncl d hnm) f).IsDiag := by
    simpa only [Sym2.isDiag_map (interactionBoxVertexIncl d hnm).injective]
      using hnonDiag
  simpa [interactionBoxGraph] using hmapped

theorem interactionBoxTransportedEdges_ambient_image (d : Nat)
    {n m : Nat} (hnm : n ≤ m)
    (E : Finset (Sym2 (interactionBoxVertices d n))) :
    sym2FinsetMap (Function.Embedding.subtype
      (fun x : Site d => x ∈ interactionBoxVertices d m))
      (interactionBoxTransportedEdges d hnm E) =
    sym2FinsetMap (Function.Embedding.subtype
      (fun x : Site d => x ∈ interactionBoxVertices d n)) E := by
  unfold interactionBoxTransportedEdges sym2FinsetMap
  rw [Finset.map_map]
  apply congrArg (fun f : Sym2 (interactionBoxVertices d n) ↪
    Sym2 (Site d) => E.map f)
  apply Function.Embedding.ext
  intro e
  induction e using Sym2.inductionOn with
  | _ x y => rfl

theorem interactionBoxSpinSupport_map_base (d : Nat) {n m : Nat}
    (hnm : n ≤ m) (A : Finset (interactionBoxVertices d n)) :
    interactionBoxSpinSupport d m
        (A.map (Function.Embedding.subtype
          (fun x : Site d => x ∈ interactionBoxVertices d n))) =
      A.map (interactionBoxVertexIncl d hnm) := by
  ext x
  simp only [interactionBoxSpinSupport, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, hval⟩
    refine ⟨a, ha, ?_⟩
    apply Subtype.ext
    exact hval
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem interactionBoxCoupling_transport {d : Nat}
    (J : Sym2 (Site d) → ℝ) {n m : Nat} (hnm : n ≤ m)
    (e : Sym2 (interactionBoxVertices d n)) :
    interactionBoxCoupling J m
        (Sym2.map (interactionBoxVertexIncl d hnm) e) =
      interactionBoxCoupling J n e := by
  induction e using Sym2.inductionOn with
  | _ x y => rfl

theorem bond_transport {d : Nat} {n m : Nat} (hnm : n ≤ m)
    (s : ConfigSpace (interactionBoxVertices d m))
    (e : Sym2 (interactionBoxVertices d n)) :
    bond s (Sym2.map (interactionBoxVertexIncl d hnm) e) =
      bond (fun x => s (interactionBoxVertexIncl d hnm x)) e := by
  induction e using Sym2.inductionOn with
  | _ x y => rfl

theorem spinProd_transport {d : Nat} {n m : Nat} (hnm : n ≤ m)
    (s : ConfigSpace (interactionBoxVertices d m))
    (A : Finset (interactionBoxVertices d n)) :
    spinProd A (fun x => s (interactionBoxVertexIncl d hnm x)) =
      spinProd (A.map (interactionBoxVertexIncl d hnm)) s := by
  unfold spinProd
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro x hx
  rfl

theorem weightedEdgeSpinSum_transport {d : Nat}
    (J : Sym2 (Site d) → ℝ) (beta : ℝ) {n m : Nat}
    (hnm : n ≤ m) (E : Finset (Sym2 (interactionBoxVertices d n)))
    (s : ConfigSpace (interactionBoxVertices d m)) :
    weightedEdgeSpinSum beta (interactionBoxCoupling J m)
        (interactionBoxTransportedEdges d hnm E) s =
      weightedEdgeSpinSum beta (interactionBoxCoupling J n) E
        (fun x => s (interactionBoxVertexIncl d hnm x)) := by
  unfold weightedEdgeSpinSum interactionBoxTransportedEdges sym2FinsetMap
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e he
  change beta * interactionBoxCoupling J m
      (Sym2.map (interactionBoxVertexIncl d hnm) e) *
        bond s (Sym2.map (interactionBoxVertexIncl d hnm) e) = _
  rw [interactionBoxCoupling_transport J hnm,
    bond_transport hnm]


theorem exp_neg_weightedEdgeSpinSum_transport_expansion {d : Nat}
    (J : Sym2 (Site d) → ℝ) (beta : ℝ) {n m : Nat}
    (hnm : n ≤ m) (E : Finset (Sym2 (interactionBoxVertices d n)))
    (hEdiag : ∀ e ∈ E, ¬e.IsDiag)
    (s : ConfigSpace (interactionBoxVertices d m)) :
    Real.exp (-weightedEdgeSpinSum beta (interactionBoxCoupling J m)
        (interactionBoxTransportedEdges d hnm E) s) =
      ∑ T ∈ E.powerset,
        weightedEdgeExpansionCoeff beta (interactionBoxCoupling J n) E T *
          spinProd ((edgeBoundary (E \ T)).map
            (interactionBoxVertexIncl d hnm)) s := by
  rw [weightedEdgeSpinSum_transport J beta hnm E s,
    exp_neg_weightedEdgeSpinSum_eq_spinProd_sum
      beta (interactionBoxCoupling J n) E hEdiag]
  apply Finset.sum_congr rfl
  intro T hT
  rw [spinProd_transport hnm]

theorem expJ_transport_expansion {d : Nat}
    (J : Sym2 (Site d) → ℝ) (beta : ℝ) {n m : Nat}
    (hnm : n ≤ m) (E : Finset (Sym2 (interactionBoxVertices d n)))
    (hEdiag : ∀ e ∈ E, ¬e.IsDiag) :
    expJ (interactionBoxGraph d m).edgeFinset
        (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0)
        (fun s => Real.exp (-weightedEdgeSpinSum beta
          (interactionBoxCoupling J m)
          (interactionBoxTransportedEdges d hnm E) s)) =
      ∑ T ∈ E.powerset,
        weightedEdgeExpansionCoeff beta (interactionBoxCoupling J n) E T *
          expJ (interactionBoxGraph d m).edgeFinset
            (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0)
            (spinProd ((edgeBoundary (E \ T)).map
              (interactionBoxVertexIncl d hnm))) := by
  unfold expJ
  have hnum :
      (∑ s : ConfigSpace (interactionBoxVertices d m),
        Real.exp (-weightedEdgeSpinSum beta (interactionBoxCoupling J m)
          (interactionBoxTransportedEdges d hnm E) s) *
          wJ (interactionBoxGraph d m).edgeFinset
            (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0) s) =
      ∑ T ∈ E.powerset,
        weightedEdgeExpansionCoeff beta (interactionBoxCoupling J n) E T *
          ∑ s : ConfigSpace (interactionBoxVertices d m),
            spinProd ((edgeBoundary (E \ T)).map
              (interactionBoxVertexIncl d hnm)) s *
              wJ (interactionBoxGraph d m).edgeFinset
                (fun e => beta * interactionBoxCoupling J m e)
                (fun _ => 0) s := by
    simp_rw [exp_neg_weightedEdgeSpinSum_transport_expansion
      J beta hnm E hEdiag]
    calc
      (∑ s : ConfigSpace (interactionBoxVertices d m),
        (∑ T ∈ E.powerset,
          weightedEdgeExpansionCoeff beta (interactionBoxCoupling J n) E T *
            spinProd ((edgeBoundary (E \ T)).map
              (interactionBoxVertexIncl d hnm)) s) *
          wJ (interactionBoxGraph d m).edgeFinset
            (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0) s) =
        ∑ s : ConfigSpace (interactionBoxVertices d m),
          ∑ T ∈ E.powerset,
            weightedEdgeExpansionCoeff beta (interactionBoxCoupling J n) E T *
              (spinProd ((edgeBoundary (E \ T)).map
                (interactionBoxVertexIncl d hnm)) s *
                wJ (interactionBoxGraph d m).edgeFinset
                  (fun e => beta * interactionBoxCoupling J m e)
                  (fun _ => 0) s) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro T hT
          ring
      _ = ∑ T ∈ E.powerset,
          ∑ s : ConfigSpace (interactionBoxVertices d m),
            weightedEdgeExpansionCoeff beta (interactionBoxCoupling J n) E T *
              (spinProd ((edgeBoundary (E \ T)).map
                (interactionBoxVertexIncl d hnm)) s *
                wJ (interactionBoxGraph d m).edgeFinset
                  (fun e => beta * interactionBoxCoupling J m e)
                  (fun _ => 0) s) := by
          rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [← Finset.mul_sum]
  rw [hnum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T hT
  ring

theorem cosh_product_transport {d : Nat}
    (J : Sym2 (Site d) → ℝ) (beta : ℝ) {n m : Nat}
    (hnm : n ≤ m) (E : Finset (Sym2 (interactionBoxVertices d n))) :
    (∏ e ∈ interactionBoxTransportedEdges d hnm E,
        Real.cosh (beta * interactionBoxCoupling J m e)) =
      ∏ e ∈ E, Real.cosh (beta * interactionBoxCoupling J n e) := by
  unfold interactionBoxTransportedEdges sym2FinsetMap
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro e he
  change Real.cosh (beta * interactionBoxCoupling J m
    (Sym2.map (interactionBoxVertexIncl d hnm) e)) = _
  rw [interactionBoxCoupling_transport J hnm]

end StatMech.FrontierB
