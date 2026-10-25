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
import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeParityLimit.Part5
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Ising Lattice

theorem finiteInteractionEdges_subset_box {d : Nat}
    (F : Finset (Sym2 (Site d))) :
    ∃ N, ∀ e ∈ F, ∀ x ∈ e, x ∈ box d N := by
  obtain ⟨N, hN⟩ := finite_subset_box
    (interactionEdgeVertexSupport F : Set (Site d))
    (interactionEdgeVertexSupport F).finite_toSet
  refine ⟨N, ?_⟩
  intro e he x hx
  apply hN
  exact Finset.mem_biUnion.mpr ⟨e, he, by simpa using hx⟩


theorem generalFreeBoxCurrentMeasure_parityAvoid_full_tendsto {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d))) (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
    ∃ L : ℝ≥0∞, Tendsto
      (fun n => (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityAvoidCylinder F)) atTop (nhds L) := by
  obtain ⟨N, hFN⟩ := finiteInteractionEdges_subset_box F
  let E : Finset (Sym2 (interactionBoxVertices d N)) :=
    interactionBoxLiftedEdges F hFN
  have hE : E ⊆ (interactionBoxGraph d N).edgeFinset :=
    interactionBoxLiftedEdges_subset_edgeFinset F hFN hFdiag
  have hEdiag : ∀ e ∈ E, ¬e.IsDiag := fun e he =>
    (interactionBoxGraph d N).not_isDiag_of_mem_edgeFinset (hE he)
  have hEambient :
      sym2FinsetMap (Function.Embedding.subtype
        (fun x : Site d => x ∈ interactionBoxVertices d N)) E = F :=
    interactionBoxLiftedEdges_ambient_image F hFN
  let c : ℝ := ∏ e ∈ E,
    Real.cosh (beta * interactionBoxCoupling J N e)
  let term (T : Finset (Sym2 (interactionBoxVertices d N))) (k : Nat) : ℝ :=
    expJ (interactionBoxGraph d (k + N)).edgeFinset
      (fun e => beta * interactionBoxCoupling J (k + N) e) (fun _ => 0)
      (spinProd ((edgeBoundary (E \ T)).map
        (interactionBoxVertexIncl d (Nat.le_add_left N k))))
  have hterm (T : Finset (Sym2 (interactionBoxVertices d N))) :
      ∃ L : ℝ, Tendsto (term T) atTop (nhds L) := by
    let A : Finset (Site d) :=
      (edgeBoundary (E \ T)).map (Function.Embedding.subtype
        (fun x : Site d => x ∈ interactionBoxVertices d N))
    obtain ⟨L, hfull⟩ := generalInteractionBox_spinProd_tendsto
      J hJ beta hbeta.le A
    have htail := (tendsto_add_atTop_iff_nat N).2 hfull
    refine ⟨L, ?_⟩
    apply htail.congr'
    filter_upwards [] with k
    unfold term A
    rw [interactionBoxSpinSupport_map_base]
  choose ell hell using hterm
  let r : ℝ := ∑ T ∈ E.powerset,
    weightedEdgeExpansionCoeff beta (interactionBoxCoupling J N) E T * ell T
  have hpoly : Tendsto
      (fun k => ∑ T ∈ E.powerset,
        weightedEdgeExpansionCoeff beta (interactionBoxCoupling J N) E T *
          term T k) atTop (nhds r) := by
    have hs := tendsto_finsetSum E.powerset (fun T hT =>
      (hell T).const_mul
        (weightedEdgeExpansionCoeff beta (interactionBoxCoupling J N) E T))
    simpa only [r] using hs
  have hreal : Tendsto
      (fun k => (∑ T ∈ E.powerset,
        weightedEdgeExpansionCoeff beta (interactionBoxCoupling J N) E T *
          term T k) * c) atTop (nhds (r * c)) :=
    hpoly.mul_const c
  have hofReal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  refine ⟨ENNReal.ofReal (r * c), (tendsto_add_atTop_iff_nat N).1 ?_⟩
  apply hofReal.congr'
  filter_upwards [] with k
  let hNk : N ≤ k + N := Nat.le_add_left N k
  let Ek : Finset (Sym2 (interactionBoxVertices d (k + N))) :=
    interactionBoxTransportedEdges d hNk E
  have hEk : Ek ⊆ (interactionBoxGraph d (k + N)).edgeFinset :=
    interactionBoxTransportedEdges_subset_edgeFinset d hNk E hE
  have himage :
      sym2FinsetMap (Function.Embedding.subtype
        (fun x : Site d => x ∈ interactionBoxVertices d (k + N))) Ek = F := by
    exact (interactionBoxTransportedEdges_ambient_image d hNk E).trans hEambient
  have hmass := generalFreeBoxCurrentMeasure_parityAvoid_edgeImage
    J hJ beta hbeta Ek hEk
  rw [himage] at hmass
  rw [hmass, expJ_transport_expansion J beta hNk E hEdiag,
    cosh_product_transport J beta hNk E]
  rfl

theorem diagonal_not_mem_range_interactionBoxEdgeIncl
    (d n : Nat) (e : Sym2 (Site d)) (he : e.IsDiag) :
    e ∉ Set.range (interactionBoxEdgeIncl d n) := by
  rintro ⟨f, rfl⟩
  have hsource : ¬f.1.IsDiag :=
    (interactionBoxGraph d n).not_isDiag_of_mem_edgeFinset f.2
  exact hsource ((Sym2.isDiag_map Subtype.val_injective).mp he)

theorem extendInteractionBoxCurrent_diag_zero
    (d n : Nat) (m : EdgeCurrent (interactionBoxGraph d n))
    (e : Sym2 (Site d)) (he : e.IsDiag) :
    extendInteractionBoxCurrent d n m e = 0 := by
  exact extendInteractionBoxCurrent_outside d n m e
    (diagonal_not_mem_range_interactionBoxEdgeIncl d n e he)

end StatMech.FrontierB
