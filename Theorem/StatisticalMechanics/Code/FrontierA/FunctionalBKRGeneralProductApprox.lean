/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductFinite
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductApprox
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


theorem IsFiniteCoordinateSet.measurableSet {A : Set (∀ e, S e)}
    (hA : IsFiniteCoordinateSet A) : MeasurableSet A := by
  obtain ⟨n, q, B, hq, rfl⟩ := hA
  exact (Set.toFinite B).measurableSet.preimage
    (measurable_pi_lambda _ fun e => (hq e).comp (measurable_pi_apply e))

theorem isFiniteCoordinateSet_empty :
    IsFiniteCoordinateSet (∅ : Set (∀ e, S e)) := by
  let n : E → ℕ := fun _ => 1
  let q : ∀ e, S e → Fin (n e) := fun _ _ => 0
  refine ⟨n, q, ∅, fun _ => measurable_const, ?_⟩
  simp

theorem IsFiniteCoordinateSet.union {A B : Set (∀ e, S e)}
    (hA : IsFiniteCoordinateSet A) (hB : IsFiniteCoordinateSet B) :
    IsFiniteCoordinateSet (A ∪ B) := by
  classical
  obtain ⟨n, q, C, hq, rfl⟩ := hA
  obtain ⟨m, r, D, hr, rfl⟩ := hB
  let k : E → ℕ := fun e => n e * m e
  let qr : ∀ e, S e → Fin (k e) := fun e x =>
    finProdFinEquiv (q e x, r e x)
  let unpair : (∀ e, Fin (k e)) → ∀ e, Fin (n e) × Fin (m e) :=
    fun y e => finProdFinEquiv.symm (y e)
  let U : Set (∀ e, Fin (k e)) :=
    {y | (fun e => (unpair y e).1) ∈ C ∨ (fun e => (unpair y e).2) ∈ D}
  refine ⟨k, qr, U, ?_, ?_⟩
  · intro e
    exact (measurable_of_finite finProdFinEquiv).comp
      (Measurable.prod (hq e) (hr e))
  · ext x
    simpa only [Set.mem_union, Set.mem_preimage, U, Set.mem_setOf_eq,
      unpair, qr, Equiv.symm_apply_apply]

theorem IsFiniteCoordinateSet.diff {A B : Set (∀ e, S e)}
    (hA : IsFiniteCoordinateSet A) (hB : IsFiniteCoordinateSet B) :
    IsFiniteCoordinateSet (A \ B) := by
  classical
  obtain ⟨n, q, C, hq, rfl⟩ := hA
  obtain ⟨m, r, D, hr, rfl⟩ := hB
  let k : E → ℕ := fun e => n e * m e
  let qr : ∀ e, S e → Fin (k e) := fun e x =>
    finProdFinEquiv (q e x, r e x)
  let unpair : (∀ e, Fin (k e)) → ∀ e, Fin (n e) × Fin (m e) :=
    fun y e => finProdFinEquiv.symm (y e)
  let V : Set (∀ e, Fin (k e)) :=
    {y | (fun e => (unpair y e).1) ∈ C ∧ (fun e => (unpair y e).2) ∉ D}
  refine ⟨k, qr, V, ?_, ?_⟩
  · intro e
    exact (measurable_of_finite finProdFinEquiv).comp
      (Measurable.prod (hq e) (hr e))
  · ext x
    simpa only [Set.mem_diff, Set.mem_preimage, V, Set.mem_setOf_eq,
      unpair, qr, Equiv.symm_apply_apply]

theorem isSetRing_isFiniteCoordinateSet :
    IsSetRing {A : Set (∀ e, S e) | IsFiniteCoordinateSet A} where
  empty_mem := isFiniteCoordinateSet_empty
  union_mem := by
    intro s t hs ht
    exact hs.union ht
  diff_mem := by
    intro s t hs ht
    exact hs.diff ht

theorem rectangle_isFiniteCoordinateSet
    (s : ∀ e, Set (S e)) (hs : ∀ e, MeasurableSet (s e)) :
    IsFiniteCoordinateSet (Set.pi Set.univ s) := by
  classical
  let n : E → ℕ := fun _ => 2
  let q : ∀ e, S e → Fin (n e) := fun e x =>
    if x ∈ s e then 1 else 0
  let B : Set (∀ e, Fin (n e)) := {y | ∀ e, y e = 1}
  refine ⟨n, q, B, ?_, ?_⟩
  · intro e
    exact measurable_const.ite (hs e) measurable_const
  · ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_preimage, B,
      Set.mem_setOf_eq, q]
    constructor
    · intro hx e
      simp [hx e]
    · intro hx e
      by_contra hnot
      have hv := congrArg Fin.val (hx e)
      simp [hnot, n] at hv

theorem generateFrom_isFiniteCoordinateSet :
    (inferInstance : MeasurableSpace (∀ e, S e)) =
      MeasurableSpace.generateFrom
        {A : Set (∀ e, S e) | IsFiniteCoordinateSet A} := by
  apply le_antisymm
  · rw [← generateFrom_pi]
    apply MeasurableSpace.generateFrom_mono
    intro A hA
    obtain ⟨s, hs, rfl⟩ := hA
    apply rectangle_isFiniteCoordinateSet s
    intro e
    exact hs e (Set.mem_univ e)
  · apply MeasurableSpace.generateFrom_le
    intro A hA
    exact hA.measurableSet

theorem exists_finiteCoordinateSet_symmDiff_lt
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    {A : Set (∀ e, S e)} (hA : MeasurableSet A)
    {eps : ℝ≥0∞} (heps : 0 < eps) :
    ∃ B, IsFiniteCoordinateSet B ∧
      Measure.pi mu (B ∆ A) < eps := by
  have huniv : IsFiniteCoordinateSet (Set.univ : Set (∀ e, S e)) :=
    by simpa only [Set.pi_univ] using
      (rectangle_isFiniteCoordinateSet (S := S)
        (fun _ => Set.univ) (fun _ => MeasurableSet.univ))
  have hcover : ∃ D : Set (Set (∀ e, S e)), D.Countable ∧
      D ⊆ {B | IsFiniteCoordinateSet B} ∧
      Measure.pi mu (Set.sUnion D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · simpa using huniv
    · simp
  exact exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    isSetRing_isFiniteCoordinateSet hcover
      generateFrom_isFiniteCoordinateSet hA heps


end StatMech.FrontierA
