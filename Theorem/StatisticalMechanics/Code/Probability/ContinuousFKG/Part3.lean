/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Instance.StatisticalMechanics.Code.Probability.ContinuousFKG
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech

namespace Probability

set_option linter.unusedSectionVars false


theorem hasFKG_pi_unitMeasure (n : ℕ) :
    HasFKG (Measure.pi (fun _ : Fin n => unitMeasure)) := by
  induction n with
  | zero =>
      
      exact hasFKG_subsingleton _
  | succ n ih =>
      
      have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => unitMeasure) 0
      
      
      have hstep : HasFKG (((fun _ : Fin (n + 1) => unitMeasure) 0).prod
          (Measure.pi fun j : Fin n =>
            (fun _ : Fin (n + 1) => unitMeasure) ((0 : Fin (n + 1)).succAbove j))) :=
        prod_fkg_step unitMeasure _ (hasFKG_real unitMeasure) ih
      exact hasFKG_of_orderIso _ _ _ hmp (piFinSuccAbove_symm_mono n) hstep


theorem continuous_fkg (n : ℕ)
    {f g : (Fin n → ℝ) → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    {Cf Cg : ℝ} (hfC : ∀ x, |f x| ≤ Cf) (hgC : ∀ x, |g x| ≤ Cg)
    (hf : Monotone f) (hg : Monotone g) :
    (∫ x, f x ∂(Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))))
      * (∫ x, g x ∂(Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))))
    ≤ ∫ x, f x * g x ∂(Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) :=
  hasFKG_pi_unitMeasure n f g hfm hgm ⟨Cf, hfC⟩ ⟨Cg, hgC⟩ hf hg

end Probability
end StatMech
