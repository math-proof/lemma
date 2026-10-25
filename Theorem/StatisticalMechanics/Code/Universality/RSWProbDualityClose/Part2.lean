/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Theorem.StatisticalMechanics.Code.Universality.KestenHalf
import Theorem.StatisticalMechanics.Code.TwoDim.SelfDualDichotomy
import Def.StatisticalMechanics.Code.Universality.RSWProbDualityClose
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box


theorem rpd_reindexInv_measurable : Measurable rpd_reindexInv :=
  (MeasurableEquiv.piCongrLeft (fun _ => Bool) crossEdge.symm).measurable


theorem rpd_map_reindexInv : Measure.map rpd_reindexInv halfMeasure = halfMeasure := by
  rw [rpd_reindexInv, halfMeasure]
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure (2⁻¹ : ℝ≥0) half_le_one) crossEdge.symm


theorem rpd_reindexInv_dualConfig :
    rpd_reindexInv ∘ dualConfig = (fun (η : ConfigSpace (Sym2 (Site 2))) e => !(η e)) := by
  funext ω e
  simp only [Function.comp_apply, rpd_reindexInv]
  have h := Equiv.piCongrLeft_apply_apply (fun _ => Bool) crossEdge.symm (dualConfig ω)
    (crossEdge e)
  simp only [Equiv.symm_apply_apply] at h
  rw [h, dualConfig, Equiv.symm_apply_apply]


theorem rpd_selfDualDichotomy_nonvacuous :
    ∃ (H : Set (ConfigSpace (Sym2 (Site 2))))
      (R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))),
      MeasurableSet H ∧ Measurable R ∧ Measure.map R halfMeasure = halfMeasure ∧
        Hᶜ = (R ∘ dualConfig) ⁻¹' H := by
  classical
  refine ⟨{ω | ω (s(![0,0],![1,0]) : Sym2 (Site 2)) = true}, rpd_reindexInv, ?_,
    rpd_reindexInv_measurable, rpd_map_reindexInv, ?_⟩
  · exact (measurableSet_singleton true).preimage (measurable_pi_apply _)
  · rw [rpd_reindexInv_dualConfig]
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_preimage, Bool.not_eq_true]
    constructor
    · intro h; simp [h]
    · intro h; simpa using h


theorem rpd_square_crossing_half_of_selfDualDichotomy (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : (horizontalCrossingEvent 0 n 0 n)ᶜ
              = (R ∘ dualConfig) ⁻¹' (horizontalCrossingEvent 0 n 0 n)) :
    halfMeasure.real (horizontalCrossingEvent 0 n 0 n) = 1 / 2 :=
  half_crossingProb_of_selfDual_dichotomy hmeasH hRmeas hRpres hdich


theorem rpd_square_crossing_le_and_ge_half_of_selfDualDichotomy (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : (horizontalCrossingEvent 0 n 0 n)ᶜ
              = (R ∘ dualConfig) ⁻¹' (horizontalCrossingEvent 0 n 0 n)) :
    halfMeasure.real (horizontalCrossingEvent 0 n 0 n) ≤ 1 / 2 ∧
      (1 : ℝ) / 2 ≤ halfMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
  have h := rpd_square_crossing_half_of_selfDualDichotomy n hmeasH hRmeas hRpres hdich
  exact ⟨le_of_eq h, ge_of_eq h⟩

end Universality
end StatMech
