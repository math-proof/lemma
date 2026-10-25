/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianNewmanRootControl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Structure.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanRootControl
open scoped BigOperators


namespace StatMech.FrontierA

theorem NewmanRootCumulantRepresentation.newmanFourthCumulantControl
    {cumulants : Nat → Nat → Real}
    (hroot : NewmanRootCumulantRepresentation cumulants) :
    NewmanFourthCumulantControl cumulants := by
  refine ⟨hroot.order_zero, hroot.odd_order, ?_⟩
  intro scale halfOrder hhalf
  let roots := hroot.roots scale
  have hnonneg : ∀ i, 0 ≤ roots i :=
    hroot.roots_nonneg scale
  have hsummable : Summable roots := hroot.roots_summable scale
  have hsum : 0 ≤ ∑' i, roots i := tsum_nonneg hnonneg
  have hsq : 0 ≤ ∑' i, roots i ^ 2 := tsum_nonneg fun _ => by positivity
  have hfactorial : 0 ≤ (Nat.factorial (2 * halfOrder) : Real) := by
    positivity
  have hpowers := tsum_pow_le_sq_tsum_mul_tsum_pow
    roots halfOrder hhalf hnonneg hsummable
  have hsqFourth : (∑' i, roots i ^ 2) ≤
      |cumulants scale 4| := by
    calc
      (∑' i, roots i ^ 2) ≤
          12 * (∑' i, roots i ^ 2) := by nlinarith
      _ ≤ |cumulants scale 4| := hroot.fourth_mass scale
  have hsumVariance : (∑' i, roots i) ^ (halfOrder - 2) ≤
      (1 + |cumulants scale 2|) ^ (halfOrder - 2) :=
    pow_le_pow_left₀ hsum (hroot.variance_mass scale) (halfOrder - 2)
  calc
    |cumulants scale (2 * halfOrder)| ≤
        (Nat.factorial (2 * halfOrder) : Real) *
          (∑' i, roots i ^ halfOrder) :=
      hroot.even_power_sum scale halfOrder hhalf
    _ ≤ (Nat.factorial (2 * halfOrder) : Real) *
          ((∑' i, roots i ^ 2) *
            (∑' i, roots i) ^ (halfOrder - 2)) :=
      mul_le_mul_of_nonneg_left hpowers hfactorial
    _ ≤ (Nat.factorial (2 * halfOrder) : Real) *
          (|cumulants scale 4| *
            (1 + |cumulants scale 2|) ^ (halfOrder - 2)) := by
      gcongr
    _ = (Nat.factorial (2 * halfOrder) : Real) *
          |cumulants scale 4| *
            (1 + |cumulants scale 2|) ^ (halfOrder - 2) := by ring

end StatMech.FrontierA
