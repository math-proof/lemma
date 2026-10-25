/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IVTranslationInvariance.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

variable {d : ℕ}


noncomputable def isd_decayFun (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) (n : ℕ) : ℝ :=
  (∫ x, f x ∂(μ n : Measure _)) - (∫ x, f (shift g x) ∂(μ n : Measure _))


end FK
end StatMech
