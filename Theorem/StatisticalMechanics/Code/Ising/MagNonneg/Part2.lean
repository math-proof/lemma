/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MagNonneg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Def.StatisticalMechanics.Code.Ising.MagNonneg
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


@[simp] theorem spinBCF_apply (x : Site d) (ω : ConfigSpace (Site d)) :
    spinBCF x ω = spin ω x := rfl


theorem integral_spinBCF_eq (d : ℕ) (β : ℝ) :
    ∫ ω, (spinBCF (origin d)) ω ∂(plusState d β 0 : Measure (ConfigSpace (Site d)))
      = magnetization d β := by
  rfl


theorem nonneg_integral_of_weakLimit
    {μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
    {ν : ProbabilityMeasure (ConfigSpace (Site d))}
    (h : WeakConvergesTo μ ν) (f : ConfigSpace (Site d) →ᵇ ℝ)
    (hpos : ∀ n, 0 ≤ ∫ ω, f ω ∂(μ n : Measure (ConfigSpace (Site d)))) :
    0 ≤ ∫ ω, f ω ∂(ν : Measure (ConfigSpace (Site d))) :=
  ge_of_tendsto (h.tendsto_integral f) (Filter.Eventually.of_forall hpos)


theorem magnetization_nonneg_of_fv (d : ℕ) (β : ℝ)
    (hfv : ∀ n, 0 ≤ ∫ ω, spin ω (origin d)
      ∂(plusMeasure d n β 0 : Measure (ConfigSpace (Site d)))) :
    0 ≤ magnetization d β := by
  
  obtain ⟨φ, _hφ, htends⟩ := plusState_isInfiniteVolumeState d β 0
  
  have hpos : ∀ n, 0 ≤ ∫ ω, (spinBCF (origin d)) ω
      ∂((fun n => plusMeasure d n β 0) (φ n) : Measure (ConfigSpace (Site d))) :=
    fun n => by simpa only [spinBCF_apply] using hfv (φ n)
  have hlim : 0 ≤ ∫ ω, (spinBCF (origin d)) ω
      ∂(plusState d β 0 : Measure (ConfigSpace (Site d))) :=
    nonneg_integral_of_weakLimit htends (spinBCF (origin d)) hpos
  rwa [integral_spinBCF_eq] at hlim


theorem hmag_nonneg_of_fv (d : ℕ)
    (hfv : ∀ β, ∀ n, 0 ≤ ∫ ω, spin ω (origin d)
      ∂(plusMeasure d n β 0 : Measure (ConfigSpace (Site d)))) :
    ∀ β, 0 ≤ magnetization d β :=
  fun β => magnetization_nonneg_of_fv d β (hfv β)

end Ising
end StatMech
