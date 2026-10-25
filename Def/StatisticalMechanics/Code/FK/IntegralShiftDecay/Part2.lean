/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IVTranslationInvariance.Part2
import Theorem.StatisticalMechanics.Code.FK.IntegralShiftDecay
open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

variable {d : ℕ}


def isd_wiredDenseDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∃ D : Set ((ConfigSpace (Sym2 (Site d))) →ᵇ ℝ), Dense D ∧
    ∀ f' ∈ D,
      Tendsto (isd_decayFun (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) g f')
        atTop (𝓝 0)


def isd_freeDenseDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∃ D : Set ((ConfigSpace (Sym2 (Site d))) →ᵇ ℝ), Dense D ∧
    ∀ f' ∈ D,
      Tendsto (isd_decayFun (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) g f')
        atTop (𝓝 0)


end FK
end StatMech
