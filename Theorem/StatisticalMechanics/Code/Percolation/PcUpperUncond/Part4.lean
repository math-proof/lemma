/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PcUpper.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Def.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part3
open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Percolation

open StatMech.Lattice


open Classical in


theorem cyclesAtLen_card (ℓ : ℕ) : (cyclesAtLen ℓ).card ≤ 2 * ℓ * 4 ^ ℓ := by
  unfold cyclesAtLen
  calc ((anchorFinset ℓ).sigma
          (fun u => ((hypercubicLattice 2).finsetWalkLength ℓ u u).filter (·.IsCycle))).card
      ≤ ((anchorFinset ℓ).sigma
          (fun u => (hypercubicLattice 2).finsetWalkLength ℓ u u)).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_sigma] at hx ⊢
        exact ⟨hx.1, Finset.filter_subset _ _ hx.2⟩
    _ ≤ (anchorFinset ℓ).card * (2 * 2) ^ ℓ := card_circuits_based_in_le_pow 2 _ ℓ
    _ ≤ (2 * ℓ) * 4 ^ ℓ := by
        apply Nat.mul_le_mul (anchorFinset_card ℓ); norm_num


open Classical in


theorem measure_cyclesAtLen_le (p : NNReal) (hp : p ≤ 1) (ℓ : ℕ) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp)
        (⋃ σ ∈ cyclesAtLen ℓ, closedCircuitEvent σ.2)
      ≤ (2 * ℓ * 4 ^ ℓ : ℕ) * ((1 - p : NNReal) : ENNReal) ^ ℓ := by
  calc (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp)
          (⋃ σ ∈ cyclesAtLen ℓ, closedCircuitEvent σ.2)
      ≤ ∑ σ ∈ cyclesAtLen ℓ, (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp)
            (closedCircuitEvent σ.2) := measure_biUnion_finset_le _ _
    _ = ∑ _σ ∈ cyclesAtLen ℓ, ((1 - p : NNReal) : ENNReal) ^ ℓ := by
        apply Finset.sum_congr rfl
        intro σ hσ
        unfold cyclesAtLen at hσ
        rw [Finset.mem_sigma, Finset.mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hσ
        obtain ⟨_, hlen, hcyc⟩ := hσ
        rw [measure_closedCircuitEvent_cycle p hp σ.2 hcyc, hlen]
    _ = (cyclesAtLen ℓ).card * ((1 - p : NNReal) : ENNReal) ^ ℓ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * ℓ * 4 ^ ℓ : ℕ) * ((1 - p : NNReal) : ENNReal) ^ ℓ := by
        apply mul_le_mul' _ (le_refl _)
        exact_mod_cast cyclesAtLen_card ℓ


end Percolation
end StatMech
