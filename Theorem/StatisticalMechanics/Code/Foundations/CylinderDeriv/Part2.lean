/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Russo
import Def.StatisticalMechanics.Code.Foundations.CylinderDeriv
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal


namespace StatMech

variable {E : Type*} [Countable E] [DecidableEq E]


omit [Countable E] in
@[simp] lemma restrict_extendOff (F : Finset E) (ω : ConfigSpace E) (η : ConfigSpace ↥F) :
    F.restrict (extendOff F ω η) = η := by
  funext j; simp [Finset.restrict, extendOff, j.2]

omit [Countable E] [DecidableEq E] in


lemma eq_cylinder_restrict_image (A : Set (ConfigSpace E)) (F : Finset E)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E)) :
    A = cylinder F (F.restrict '' A) := by
  ext ω
  simp only [mem_cylinder, Set.mem_image]
  refine ⟨fun hω => ⟨ω, hω, rfl⟩, ?_⟩
  rintro ⟨ω', hω', heq⟩
  have hind : A.indicator (fun _ => (1 : ℝ)) ω' = A.indicator (fun _ => (1 : ℝ)) ω := by
    refine hA fun i hi => ?_
    have := congrFun heq ⟨i, hi⟩
    simpa [Finset.restrict] using this
  rw [Set.indicator_of_mem hω'] at hind
  by_contra hcon
  rw [Set.indicator_of_notMem hcon] at hind
  norm_num at hind

omit [DecidableEq E] in


lemma bernoulliProductMeasure_cylinder (p : NNReal) (hp : p ≤ 1) (F : Finset E)
    (S : Set (ConfigSpace ↥F)) :
    bernoulliProductMeasure (E := E) p hp (cylinder F S)
      = bernoulliProductMeasure (E := ↥F) p hp S := by
  unfold bernoulliProductMeasure
  rw [Measure.infinitePi_cylinder (μ := fun _ : E => bernoulliMeasure p hp) (s := F) (S := S)
        (by measurability),
      ← Measure.infinitePi_eq_pi]

omit [DecidableEq E] in


lemma realProb_cylinder (p : NNReal) (hp : p ≤ 1) (F : Finset E)
    (S : Set (ConfigSpace ↥F)) :
    (bernoulliProductMeasure (E := E) p hp).real (cylinder F S)
      = (bernoulliProductMeasure (E := ↥F) p hp).real S := by
  rw [Measure.real, Measure.real, bernoulliProductMeasure_cylinder]


theorem realProb_cylinder_eq_prob (p : NNReal) (hp : p ≤ 1)
    (A : Set (ConfigSpace E)) (F : Finset E)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E)) :
    (bernoulliProductMeasure (E := E) p hp).real A
      = prob (p : ℝ) (F.restrict '' A) := by
  conv_lhs => rw [eq_cylinder_restrict_image A F hA]
  rw [realProb_cylinder, finiteRealProb_eq_prob]


theorem realProb_cylinder_eq_finsum (p : NNReal) (hp : p ≤ 1)
    (A : Set (ConfigSpace E)) (F : Finset E)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E)) :
    (bernoulliProductMeasure (E := E) p hp).real A
      = ∑ η : ConfigSpace ↥F,
          (F.restrict '' A).indicator (fun _ => (1 : ℝ)) η
            * ∏ e : ↥F, (if η e then (p : ℝ) else 1 - p) := by
  rw [realProb_cylinder_eq_prob p hp A F hA]
  unfold prob configWeight edgeWeight
  rfl


omit [Countable E] in


theorem hasDerivAt_realProb_cylinder
    (A : Set (ConfigSpace E)) (F : Finset E) (q : ℝ) :
    HasDerivAt (fun q => prob q (F.restrict '' A))
      (∑ ω : ConfigSpace ↥F,
        (F.restrict '' A).indicator (fun _ => (1 : ℝ)) ω *
          ∑ e : ↥F, weightOff q e ω * (if ω e then (1 : ℝ) else -1)) q :=
  hasDerivAt_prob (F.restrict '' A) q

omit [Countable E] in


theorem differentiable_realProb_cylinder
    (A : Set (ConfigSpace E)) (F : Finset E) :
    Differentiable ℝ (fun q => prob q (F.restrict '' A)) :=
  fun q => (hasDerivAt_realProb_cylinder A F q).differentiableAt


omit [Countable E] in


lemma isIncreasing_restrict_image (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (F : Finset E) : IsIncreasing (F.restrict '' A) := by
  intro η η' hηη' hη
  obtain ⟨ω, hωA, rfl⟩ := hη
  refine ⟨extendOff F ω η', hA (fun j => ?_) hωA, restrict_extendOff F ω η'⟩
  by_cases hj : j ∈ F
  · simpa [extendOff, hj, Finset.restrict] using hηη' ⟨j, hj⟩
  · simp [extendOff, hj]

omit [Countable E] in


theorem hasDerivAt_realProb_cylinder_pivotal
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (F : Finset E) (q : ℝ) :
    HasDerivAt (fun q => prob q (F.restrict '' A))
      (∑ e : ↥F, pivotalProb q (F.restrict '' A) e) q :=
  hasDerivAt_prob_eq_sum_pivotalProb (F.restrict '' A) (isIncreasing_restrict_image A hA F) q

omit [Countable E] in


theorem deriv_realProb_cylinder_pivotal
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (F : Finset E) (q : ℝ) :
    deriv (fun q => prob q (F.restrict '' A)) q
      = ∑ e : ↥F, pivotalProb q (F.restrict '' A) e :=
  (hasDerivAt_realProb_cylinder_pivotal A hA F q).deriv

end StatMech
