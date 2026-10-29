/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HolleyFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.StrassenFinite.Part2
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Def.StatisticalMechanics.Code.Probability.HolleyFKG.Part2
open Finset
open scoped NNReal


namespace StatMech

namespace Probability

variable {α : Type*}


section Conditioning

variable [Fintype α] [DecidableEq α] [DistribLattice α]


theorem fkg_conditioning_domination {π : α → NNReal} (hπ : FKGCondition π)
    {S : Finset α} (hS : ∀ ⦃a b⦄, a ≤ b → a ∈ S → b ∈ S) :
    StochasticDom ((∑ a ∈ S, π a) • π) ((∑ a, π a) • restrictTo π S) := by
  set Z : NNReal := ∑ a, π a with hZ
  set ZS : NNReal := ∑ a ∈ S, π a with hZS
  
  have hmass : ∑ a, (ZS • π) a = ∑ a, (Z • restrictTo π S) a := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← hZ]
    have hsumR : ∑ a, restrictTo π S a = ZS := by
      unfold restrictTo
      rw [← Finset.sum_filter]
      congr 1
      ext a; simp
    rw [hsumR, mul_comm]
  
  have hcross : HolleyLatticeCondition ((ZS • π)) ((Z • restrictTo π S)) := by
    intro x y
    simp only [Pi.smul_apply, smul_eq_mul, restrictTo]
    by_cases hy : y ∈ S
    · have hxy : x ⊔ y ∈ S := hS le_sup_right hy
      rw [if_pos hy, if_pos hxy]
      
      have hfkg := hπ x y
      calc ZS * π x * (Z * π y)
            = (Z * ZS) * (π x * π y) := by ring
        _ ≤ (Z * ZS) * (π (x ⊓ y) * π (x ⊔ y)) := by
              gcongr
        _ = ZS * π (x ⊓ y) * (Z * π (x ⊔ y)) := by ring
    · rw [if_neg hy, mul_zero, mul_zero]
      exact zero_le'
  exact holley_domination hmass hcross

end Conditioning
end Probability
end StatMech
