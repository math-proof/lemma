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
import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeParityLimit.Part3
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Ising Lattice

theorem interactionBoxLiftedEdges_ambient_image {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n) :
    sym2FinsetMap (Function.Embedding.subtype
      (fun x : Site d => x ∈ interactionBoxVertices d n))
      (interactionBoxLiftedEdges F hFbox) = F := by
  unfold sym2FinsetMap interactionBoxLiftedEdges
  rw [Finset.map_map]
  have hemb :
      (interactionBoxLiftEdgeEmbedding F hFbox).trans
          (sym2MapEmbedding (Function.Embedding.subtype
            (fun x : Site d => x ∈ interactionBoxVertices d n))) =
        (⟨Subtype.val, Subtype.val_injective⟩ : ↑F ↪ Sym2 (Site d)) := by
    apply Function.Embedding.ext
    intro e
    exact interactionBoxLiftEdge_map_val F hFbox e
  rw [hemb]
  ext e
  simp

theorem interactionBoxLiftedEdges_subset_edgeFinset {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
    interactionBoxLiftedEdges F hFbox ⊆
      (interactionBoxGraph d n).edgeFinset := by
  intro e he
  rw [SimpleGraph.mem_edgeFinset]
  have hsource : ¬(Sym2.map Subtype.val e).IsDiag := by
    rw [interactionBoxLiftedEdges, Finset.mem_map] at he
    obtain ⟨g, hg, rfl⟩ := he
    change ¬(Sym2.map Subtype.val
      (interactionBoxLiftEdge F hFbox g)).IsDiag
    rw [interactionBoxLiftEdge_map_val]
    exact hFdiag g.1 g.2
  have hnonDiag : ¬e.IsDiag := by
    simpa only [Sym2.isDiag_map Subtype.val_injective] using hsource
  simpa [interactionBoxGraph] using hnonDiag

theorem preimage_currentParityAvoidCylinder_extendInteractionBoxCurrent
    (d n : Nat) (E : Finset (Sym2 (interactionBoxVertices d n)))
    (hE : E ⊆ (interactionBoxGraph d n).edgeFinset) :
    extendInteractionBoxCurrent d n ⁻¹'
        currentParityAvoidCylinder
          (sym2FinsetMap (Function.Embedding.subtype
            (fun x : Site d => x ∈ interactionBoxVertices d n)) E) =
      {m | Disjoint (currentParitySupport (interactionBoxGraph d n) m) E} := by
  ext m
  simp only [Set.mem_preimage, currentParityAvoidCylinder, Set.mem_setOf_eq]
  rw [Finset.disjoint_left]
  constructor
  · intro hall e heOdd heE'
    let i : (interactionBoxGraph d n).edgeFinset := ⟨e, hE heE'⟩
    have hodd : Odd (m i) := by
      exact (mem_currentParitySupport (interactionBoxGraph d n) m i).mp heOdd
    have hamb : Sym2.map Subtype.val e ∈
        sym2FinsetMap (Function.Embedding.subtype
          (fun x : Site d => x ∈ interactionBoxVertices d n)) E := by
      unfold sym2FinsetMap
      exact Finset.mem_map.mpr ⟨e, heE', rfl⟩
    have heven := hall (Sym2.map Subtype.val e) hamb
    have heq : extendInteractionBoxCurrent d n m
        (Sym2.map Subtype.val e) = m i := by
      exact extendInteractionBoxCurrent_included d n m i
    rw [heq] at heven
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  · intro hdis a ha
    unfold sym2FinsetMap at ha
    rw [Finset.mem_map] at ha
    obtain ⟨e, heE', rfl⟩ := ha
    let i : (interactionBoxGraph d n).edgeFinset := ⟨e, hE heE'⟩
    have hnotOdd : ¬Odd (m i) := by
      intro hodd
      exact (hdis
        ((mem_currentParitySupport (interactionBoxGraph d n) m i).mpr hodd)) heE'
    have heven : Even (m i) := Nat.not_odd_iff_even.mp hnotOdd
    change Even (extendInteractionBoxCurrent d n m
      (interactionBoxEdgeIncl d n i))
    rw [extendInteractionBoxCurrent_included d n m i]
    exact heven

theorem measurableSet_currentParityAvoidCylinder {E : Type*} [Countable E]
    (F : Finset E) : MeasurableSet (currentParityAvoidCylinder F) := by
  have hset : currentParityAvoidCylinder F =
      (restrictCurrent F) ⁻¹' {a : ↑F → Nat | ∀ e, Even (a e)} := by
    ext m
    simp [currentParityAvoidCylinder, restrictCurrent]
  rw [hset]
  exact (continuous_restrictCurrent F).measurable MeasurableSet.of_discrete


theorem generalFreeBoxCurrentMeasure_parityAvoid_edgeImage {d n : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (E : Finset (Sym2 (interactionBoxVertices d n)))
    (hE : E ⊆ (interactionBoxGraph d n).edgeFinset) :
    (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder
          (sym2FinsetMap (Function.Embedding.subtype
            (fun x : Site d => x ∈ interactionBoxVertices d n)) E)) =
      ENNReal.ofReal
        (expJ (interactionBoxGraph d n).edgeFinset
            (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0)
            (fun s => Real.exp (-weightedEdgeSpinSum beta
              (interactionBoxCoupling J n) E s)) *
          ∏ e ∈ E, Real.cosh
            (beta * interactionBoxCoupling J n e)) := by
  let A := sym2FinsetMap (Function.Embedding.subtype
    (fun x : Site d => x ∈ interactionBoxVertices d n)) E
  have hmeas : MeasurableSet (currentParityAvoidCylinder A) :=
    measurableSet_currentParityAvoidCylinder A
  calc
    (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder A) =
      (sourcelessCurrentPMF (interactionBoxGraph d n) beta
        (interactionBoxCoupling J n) hbeta.le
          (fun e => hJ (Sym2.map Subtype.val e))).toMeasure
        {m | Disjoint (currentParitySupport (interactionBoxGraph d n) m) E} := by
      change Measure.map (extendInteractionBoxCurrent d n)
        (sourcelessCurrentPMF (interactionBoxGraph d n) beta
          (interactionBoxCoupling J n) hbeta.le
            (fun e => hJ (Sym2.map Subtype.val e))).toMeasure
          (currentParityAvoidCylinder A) = _
      rw [Measure.map_apply (measurable_extendInteractionBoxCurrent d n) hmeas,
        preimage_currentParityAvoidCylinder_extendInteractionBoxCurrent
          d n E hE]
    _ = ENNReal.ofReal
        (inhomogeneousParityAvoidSum (interactionBoxGraph d n) beta
            (interactionBoxCoupling J n) E /
          inhomogeneousParityPartition (interactionBoxGraph d n) beta
            (interactionBoxCoupling J n)) :=
      sourcelessCurrentMeasure_parityAvoid_inhomogeneous
        (interactionBoxGraph d n) beta hbeta
        (interactionBoxCoupling J n)
        (fun e => hJ (Sym2.map Subtype.val e)) E
    _ = _ := by
      rw [inhomogeneousParityAvoidRatio_eq_expJ
        (interactionBoxGraph d n) beta (interactionBoxCoupling J n) E hE]

end StatMech.FrontierB
