/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKErgodicFull.Part2
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Theorem.StatisticalMechanics.Code.FK.IVTranslationInvariance
open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

variable {d : ℕ}


def ivt_wiredIntegralShiftDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ,
    Tendsto (fun n =>
        (∫ x, f x ∂((wiredFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _))
          - (∫ x, f (shift g x)
              ∂((wiredFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _)))
      atTop (𝓝 0)


def ivt_freeIntegralShiftDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ,
    Tendsto (fun n =>
        (∫ x, f x ∂((freeFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _))
          - (∫ x, f (shift g x)
              ∂((freeFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _)))
      atTop (𝓝 0)


end FK
end StatMech
