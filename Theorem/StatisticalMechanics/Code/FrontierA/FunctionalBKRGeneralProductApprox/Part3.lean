/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductFinite
import Instance.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductApprox
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


theorem measurePreserving_piRestrict
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (K : Set E) :
    MeasurePreserving (piRestrict (S := S) K) (Measure.pi mu)
      (Measure.pi fun i : {e : E // e ∈ K} => mu i) := by
  classical
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    mu (fun e => e ∈ K)
  have hfst : MeasurePreserving Prod.fst
      ((Measure.pi fun i : {e : E // e ∈ K} => mu i).prod
        (Measure.pi fun i : {e : E // e ∉ K} => mu i))
      (Measure.pi fun i : {e : E // e ∈ K} => mu i) :=
    measurePreserving_fst
  simpa only [Function.comp_apply, piRestrict, piFiberSplit] using hfst.comp hsplit


theorem IsFiniteCoordinateSet.preimage_piRestrict
    (K : Set E) {A : Set (∀ i : {e : E // e ∈ K}, S i)}
    (hA : IsFiniteCoordinateSet A) :
    IsFiniteCoordinateSet ((piRestrict (S := S) K) ⁻¹' A) := by
  classical
  obtain ⟨n, q, B, hq, rfl⟩ := hA
  let nf : E → ℕ := fun e => if he : e ∈ K then n ⟨e, he⟩ else 1
  let qf : ∀ e, S e → Fin (nf e) := fun e =>
    if he : e ∈ K then
      fun x => Fin.cast (by simp [nf, he]) (q ⟨e, he⟩ x)
    else fun _ => Fin.cast (by simp [nf, he]) (0 : Fin 1)
  let restrictFinite : (∀ e, Fin (nf e)) →
      ∀ i : {e : E // e ∈ K}, Fin (n i) := fun y i =>
    Fin.cast (by simp [nf, i.property]) (y i)
  let Bf : Set (∀ e, Fin (nf e)) := restrictFinite ⁻¹' B
  refine ⟨nf, qf, Bf, ?_, ?_⟩
  · intro e
    by_cases he : e ∈ K
    · simpa [qf, he] using
        (measurable_of_finite (Fin.cast (by simp [nf, he]))).comp (hq ⟨e, he⟩)
    · simp [qf, he]
  · ext x
    simp only [Set.mem_preimage, Bf]
    have heq : (fun i => q i (piRestrict K x i)) =
        restrictFinite (fun e => qf e (x e)) := by
      funext i
      simp [restrictFinite, qf, piRestrict, i.property]
    rw [heq]


end StatMech.FrontierA
