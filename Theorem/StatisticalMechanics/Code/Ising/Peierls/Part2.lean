/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Def.StatisticalMechanics.Code.Ising.Peierls.Part2
open MeasureTheory Filter Topology Finset
open scoped BigOperators ENNReal


set_option linter.unusedVariables false

set_option linter.style.show false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


@[simp] lemma flipInteriorEquiv_apply {n : ℕ} (τ : {x // x ∈ box d n} → Bool) :
    flipInteriorEquiv τ = flipInterior τ := rfl


@[simp] lemma flipConfig_plusField : flipConfig (plusField d) = minusField d := by
  funext y; simp [flipConfig, plusField, minusField]


@[simp] lemma flipConfig_minusField : flipConfig (minusField d) = plusField d := by
  funext y; simp [flipConfig, plusField, minusField]


lemma spin_flipConfig (s : ConfigSpace (Site d)) (x : Site d) :
    spin (flipConfig s) x = - spin s x := by
  unfold spin flipConfig; by_cases h : s x <;> simp [h]


lemma bond_flipConfig (s : ConfigSpace (Site d)) (e : Sym2 (Site d)) :
    bond (flipConfig s) e = bond s e := by
  induction e with
  | h a b =>
    simp only [bond_mk]; unfold spin flipConfig
    by_cases ha : s a <;> by_cases hb : s b <;> simp [ha, hb]


lemma glue_flipConfig {n : ℕ} (η : ConfigSpace (Site d)) (τ : {x // x ∈ box d n} → Bool) :
    flipConfig (glue η τ) = glue (flipConfig η) (flipInterior τ) := by
  funext x
  by_cases hx : x ∈ box d n
  · simp [flipConfig, glue_mem _ _ hx, flipInterior]
  · simp [flipConfig, glue_not_mem _ _ hx]


lemma fvEnergy_flip (η : ConfigSpace (Site d)) (n : ℕ) (B : Finset (Sym2 (Site d)))
    (h : ℝ) (τ : {x // x ∈ box d n} → Bool) :
    fvEnergy (flipConfig η) n B (-h) (flipInterior τ) = fvEnergy η n B h τ := by
  unfold fvEnergy
  rw [← glue_flipConfig]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl (fun e _ => bond_flipConfig _ e)
  · rw [show (∑ x ∈ boxFinset d n, spin (flipConfig (glue η τ)) x)
          = - ∑ x ∈ boxFinset d n, spin (glue η τ) x by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun x _ => spin_flipConfig _ x)]
    ring


lemma fvWeight_flip (η : ConfigSpace (Site d)) (n : ℕ) (B : Finset (Sym2 (Site d)))
    (β h : ℝ) (τ : {x // x ∈ box d n} → Bool) :
    fvWeight (flipConfig η) n B β (-h) (flipInterior τ) = fvWeight η n B β h τ := by
  unfold fvWeight; rw [fvEnergy_flip]


lemma fvZ_flip (η : ConfigSpace (Site d)) (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    fvZ (flipConfig η) n B β (-h) = fvZ η n B β h := by
  unfold fvZ
  rw [← Equiv.sum_comp (flipInteriorEquiv (d := d) (n := n))
        (fun τ => fvWeight (flipConfig η) n B β (-h) τ)]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  show fvWeight (flipConfig η) n B β (-h) (flipInterior τ) = fvWeight η n B β h τ
  rw [fvWeight_flip]


lemma fvProb_flip (η : ConfigSpace (Site d)) (n : ℕ) (B : Finset (Sym2 (Site d)))
    (β h : ℝ) (τ : {x // x ∈ box d n} → Bool) :
    fvProb (flipConfig η) n B β (-h) (flipInterior τ) = fvProb η n B β h τ := by
  unfold fvProb; rw [fvWeight_flip, fvZ_flip]


lemma measurable_flipConfig :
    Measurable (flipConfig : ConfigSpace (Site d) → ConfigSpace (Site d)) :=
  Measurable.of_eval (fun y => Measurable.of_discrete.comp (measurable_pi_apply y))


lemma continuous_flipConfig :
    Continuous (flipConfig : ConfigSpace (Site d) → ConfigSpace (Site d)) :=
  continuous_pi (fun y =>
    (continuous_of_discreteTopology (f := fun b : Bool => !b)).comp (continuous_apply y))


lemma map_finsetSum {α : Type*} [MeasurableSpace α] {f : α → α} (hf : Measurable f)
    {ι : Type*} (s : Finset ι) (μ : ι → Measure α) :
    Measure.map f (∑ i ∈ s, μ i) = ∑ i ∈ s, Measure.map f (μ i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hf, ih]


lemma map_fvMeasure_flip (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    Measure.map flipConfig (fvMeasure η n B β h)
      = fvMeasure (flipConfig η) n B β (-h) := by
  unfold fvMeasure
  rw [map_finsetSum measurable_flipConfig]
  rw [← Equiv.sum_comp (flipInteriorEquiv (d := d) (n := n))
        (fun τ => ENNReal.ofReal (fvProb (flipConfig η) n B β (-h) τ)
          • Measure.dirac (glue (flipConfig η) τ))]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Measure.map_smul, Measure.map_dirac (glue η τ)]
  show ENNReal.ofReal (fvProb η n B β h τ) • Measure.dirac (flipConfig (glue η τ))
     = ENNReal.ofReal (fvProb (flipConfig η) n B β (-h) (flipInterior τ))
        • Measure.dirac (glue (flipConfig η) (flipInterior τ))
  rw [fvProb_flip, ← glue_flipConfig]


lemma map_minusMeasure_eq_plusMeasure (n : ℕ) (β : ℝ) :
    Measure.map flipConfig
        ((minusMeasure d n β 0 : ProbabilityMeasure (ConfigSpace (Site d)))
          : Measure (ConfigSpace (Site d)))
      = ((plusMeasure d n β 0 : ProbabilityMeasure (ConfigSpace (Site d)))
          : Measure (ConfigSpace (Site d))) := by
  show Measure.map flipConfig (fvMeasure (minusField d) n (bondFinsetTouch d n) β 0)
      = fvMeasure (plusField d) n (bondFinsetTouch d n) β 0
  rw [map_fvMeasure_flip]
  simp


end Ising
end StatMech
