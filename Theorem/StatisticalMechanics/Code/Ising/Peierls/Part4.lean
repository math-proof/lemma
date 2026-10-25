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
import Def.StatisticalMechanics.Code.Ising.Peierls.Part4
open MeasureTheory Filter Topology Finset
open scoped BigOperators ENNReal


set_option linter.unusedVariables false

set_option linter.style.show false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


lemma fvMagOrigin_eq_integral (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    fvMagOrigin η n B β h
      = ∫ s, spin s (origin d) ∂(fvMeasure η n B β h) := by
  unfold fvMagOrigin fvMeasure
  rw [MeasureTheory.integral_finsetSum_measure]
  · refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [MeasureTheory.integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (fvProb_nonneg η n B β h τ)]
  · intro τ _
    refine Integrable.smul_measure ?_ (by simp)
    exact (continuous_spin_apply (origin d)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)


lemma fvMagOrigin_flip (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    fvMagOrigin (flipConfig η) n B β (-h) = - fvMagOrigin η n B β h := by
  unfold fvMagOrigin
  rw [← Finset.sum_neg_distrib,
    ← Equiv.sum_comp (flipInteriorEquiv (d := d) (n := n))
      (fun τ => fvProb (flipConfig η) n B β (-h) τ * spin (glue (flipConfig η) τ) (origin d))]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  show fvProb (flipConfig η) n B β (-h) (flipInterior τ)
        * spin (glue (flipConfig η) (flipInterior τ)) (origin d)
      = - (fvProb η n B β h τ * spin (glue η τ) (origin d))
  rw [fvProb_flip, ← glue_flipConfig, spin_flipConfig]; ring


lemma fvMagOrigin_minus_eq_neg (n : ℕ) (β : ℝ) :
    fvMagOrigin (minusField d) n (bondFinsetTouch d n) β 0
      = - fvMagOrigin (plusField d) n (bondFinsetTouch d n) β 0 := by
  have := fvMagOrigin_flip (plusField d) n (bondFinsetTouch d n) β 0
  rwa [flipConfig_plusField, neg_zero] at this


lemma fvMagOrigin_plus_eq_integral (n : ℕ) (β : ℝ) :
    fvMagOrigin (plusField d) n (bondFinsetTouch d n) β 0
      = ∫ s, spin s (origin d)
          ∂((plusMeasure d n β 0 : ProbabilityMeasure (ConfigSpace (Site d)))
              : Measure (ConfigSpace (Site d))) :=
  fvMagOrigin_eq_integral _ _ _ _ _

lemma fvMagOrigin_minus_eq_integral (n : ℕ) (β : ℝ) :
    fvMagOrigin (minusField d) n (bondFinsetTouch d n) β 0
      = ∫ s, spin s (origin d)
          ∂((minusMeasure d n β 0 : ProbabilityMeasure (ConfigSpace (Site d)))
              : Measure (ConfigSpace (Site d))) :=
  fvMagOrigin_eq_integral _ _ _ _ _


lemma plusMeasure_ne_minusMeasure_of_fvMagOrigin_ne_zero (n : ℕ) (β : ℝ)
    (hm : fvMagOrigin (plusField d) n (bondFinsetTouch d n) β 0 ≠ 0) :
    plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
  intro heq
  have hmag : fvMagOrigin (plusField d) n (bondFinsetTouch d n) β 0
      = fvMagOrigin (minusField d) n (bondFinsetTouch d n) β 0 := by
    rw [fvMagOrigin_plus_eq_integral, fvMagOrigin_minus_eq_integral, heq]
  rw [fvMagOrigin_minus_eq_neg] at hmag
  exact hm (by linarith [hmag])


theorem peierls_lro_criterion (hd : 2 ≤ d) (n : ℕ) (β : ℝ)
    (hPeierls : 0 < fvMagOrigin (plusField d) n (bondFinsetTouch d n) β 0) :
    plusMeasure d n β 0 ≠ minusMeasure d n β 0 :=
  plusMeasure_ne_minusMeasure_of_fvMagOrigin_ne_zero n β hPeierls.ne'

end Ising
end StatMech
