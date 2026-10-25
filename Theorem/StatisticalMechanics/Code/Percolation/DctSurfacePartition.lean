/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferential.Part4
import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.LastExit.Part2
import Def.StatisticalMechanics.Code.Percolation.DctSurfacePartition
open MeasureTheory Function Set SimpleGraph
open scoped NNReal ENNReal
open StatMech


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


@[simp]
theorem mem_pivotalEvent {e : Sym2 (Site d)} {A : Set (ConfigSpace (Sym2 (Site d)))}
    {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ pivotalEvent e A ↔ IsPivotal e A ω := Iff.rfl


theorem pivotalEvent_dependsOn (A : Set (ConfigSpace (Sym2 (Site d)))) (F : Finset (Sym2 (Site d)))
    (e : Sym2 (Site d))
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set (Sym2 (Site d)))) :
    DependsOn ((pivotalEvent e A).indicator (fun _ => (1 : ℝ))) (F : Set (Sym2 (Site d))) := by
  intro ω ω' h
  have hAiff : ∀ a b : ConfigSpace (Sym2 (Site d)),
      (∀ i ∈ (F : Set (Sym2 (Site d))), a i = b i) → (a ∈ A ↔ b ∈ A) := by
    intro a b hab
    by_cases ha : a ∈ A
    · refine ⟨fun _ => ?_, fun _ => ha⟩
      by_contra hb
      have := hA hab
      rw [Set.indicator_of_mem ha, Set.indicator_of_notMem hb] at this; norm_num at this
    · refine ⟨fun hc => absurd hc ha, fun hb => ?_⟩
      by_contra
      have := hA hab
      rw [Set.indicator_of_notMem ha, Set.indicator_of_mem hb] at this; norm_num at this
  have h1 : (setOpen e ω ∈ A ↔ setOpen e ω' ∈ A) := by
    apply hAiff; intro i hi
    by_cases hie : i = e
    · subst hie; simp [setOpen]
    · rw [setOpen_of_ne hie, setOpen_of_ne hie, h i hi]
  have h2 : (setClosed e ω ∈ A ↔ setClosed e ω' ∈ A) := by
    apply hAiff; intro i hi
    by_cases hie : i = e
    · subst hie; simp [setClosed]
    · rw [setClosed_of_ne hie, setClosed_of_ne hie, h i hi]
  have hpiv : IsPivotal e A ω ↔ IsPivotal e A ω' := by
    unfold IsPivotal
    rw [(propext h1 : (setOpen e ω ∈ A) = (setOpen e ω' ∈ A)),
        (propext h2 : (setClosed e ω ∈ A) = (setClosed e ω' ∈ A))]
  by_cases hmem : ω ∈ pivotalEvent e A
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hpiv.mp hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun hc => hmem (hpiv.mpr hc))]


theorem restrict_setOpen (F : Finset (Sym2 (Site d))) (e : Sym2 (Site d)) (he : e ∈ F)
    (ω : ConfigSpace (Sym2 (Site d))) :
    F.restrict (setOpen e ω) = setOpen (⟨e, he⟩ : ↥F) (F.restrict ω) := by
  funext j
  by_cases hj : j = (⟨e, he⟩ : ↥F)
  · subst hj; simp [setOpen, Finset.restrict]
  · have hje : (j : Sym2 (Site d)) ≠ e := fun hc => hj (Subtype.ext hc)
    simp only [setOpen_of_ne hj]
    show (setOpen e ω) (j : Sym2 (Site d)) = _
    rw [setOpen_of_ne hje]; rfl


theorem restrict_setClosed (F : Finset (Sym2 (Site d))) (e : Sym2 (Site d)) (he : e ∈ F)
    (ω : ConfigSpace (Sym2 (Site d))) :
    F.restrict (setClosed e ω) = setClosed (⟨e, he⟩ : ↥F) (F.restrict ω) := by
  funext j
  by_cases hj : j = (⟨e, he⟩ : ↥F)
  · subst hj; simp [setClosed, Finset.restrict]
  · have hje : (j : Sym2 (Site d)) ≠ e := fun hc => hj (Subtype.ext hc)
    simp only [setClosed_of_ne hj]
    show (setClosed e ω) (j : Sym2 (Site d)) = _
    rw [setClosed_of_ne hje]; rfl


theorem restrict_image_pivotalEvent (A : Set (ConfigSpace (Sym2 (Site d))))
    (F : Finset (Sym2 (Site d))) (e : Sym2 (Site d)) (he : e ∈ F)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set (Sym2 (Site d)))) :
    F.restrict '' (pivotalEvent e A)
      = {η : ConfigSpace ↥F | IsPivotal (⟨e, he⟩ : ↥F) (F.restrict '' A) η} := by
  have hcyl : A = cylinder F (F.restrict '' A) := eq_cylinder_restrict_image A F hA
  have memA : ∀ ω : ConfigSpace (Sym2 (Site d)), ω ∈ A ↔ F.restrict ω ∈ F.restrict '' A := by
    intro ω; conv_lhs => rw [hcyl]; rw [mem_cylinder]
  ext η
  constructor
  · rintro ⟨ω, hω, rfl⟩
    show IsPivotal (⟨e, he⟩ : ↥F) (F.restrict '' A) (F.restrict ω)
    have hω' : IsPivotal e A ω := hω
    unfold IsPivotal at hω' ⊢
    rw [← restrict_setOpen F e he ω, ← restrict_setClosed F e he ω, ← memA, ← memA]
    exact hω'
  · intro hη
    refine ⟨extendOff F (fun _ => false) η, ?_, restrict_extendOff F _ η⟩
    show IsPivotal e A (extendOff F (fun _ => false) η)
    unfold IsPivotal at hη ⊢
    rw [memA, memA, restrict_setOpen F e he, restrict_setClosed F e he, restrict_extendOff]
    exact hη


theorem pivotalProb_eq_realPivotal (p : ℝ≥0) (hp : p ≤ 1)
    (A : Set (ConfigSpace (Sym2 (Site d)))) (F : Finset (Sym2 (Site d))) (e : Sym2 (Site d))
    (he : e ∈ F)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set (Sym2 (Site d)))) :
    pivotalProb (p : ℝ) (F.restrict '' A) (⟨e, he⟩ : ↥F)
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (pivotalEvent e A) := by
  rw [realProb_cylinder_eq_prob p hp (pivotalEvent e A) F (pivotalEvent_dependsOn A F e hA),
      restrict_image_pivotalEvent A F e he hA]
  unfold pivotalProb prob
  rfl


theorem deriv_boxCrossProb_inf (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    deriv (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) (p : ℝ)
      = ∑ e : ↥(boxEdgeFinset d n),
          (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
            (pivotalEvent (↑e : Sym2 (Site d)) (boxCrossingEvent d n)) := by
  rw [deriv_boxCrossProb]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have hbridge := pivotalProb_eq_realPivotal p hp (boxCrossingEvent d n)
    (boxEdgeFinset d n) (↑e : Sym2 (Site d)) e.2 (boxCrossingEvent_dependsOn n)
  simpa using hbridge


end Percolation
end StatMech
