/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerCapacity
import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Structure.StatisticalMechanics.Code.SLE.ChainCapacity.Part2
open Complex Set Filter Topology MeasureTheory
open scoped NNReal


namespace StatMech.SLE

theorem chordalSLE_capacity_parametrized (c : CapacityParametrizedChain) :
    ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (c.chain.maps t) (2 * t) :=
  loewner_capacity_eq_of_loewnerChain c.chain c.capacity.normalized c.capacity.rate


theorem loewnerChain_hulls_increasing (c : CapacityParametrizedChain) :
    MonotoneHullFamily c.hull :=
  ⟨c.hull_isHull, c.hull_monotone⟩


theorem chordalSLE_hull_subset (c : CapacityParametrizedChain) {s t : ℝ}
    (hst : s ≤ t) : c.hull s ⊆ c.hull t :=
  subset_of_monotoneHull (loewnerChain_hulls_increasing c) hst


theorem chordalSLE_complement_antitone (c : CapacityParametrizedChain) :
    Antitone (fun t => upperHalfPlane \ c.hull t) :=
  complement_antitone_of_monotoneHull (loewnerChain_hulls_increasing c)


theorem chordalSLE_hcap_eq (c : CapacityParametrizedChain) :
    ∀ t ∈ Ici (0 : ℝ), c.coeff t = 2 * t :=
  loewner_capacity_coeff_eq c.capacity.coeff_zero c.capacity.rate


theorem chordalSLE_normalized_map_unique (c : CapacityParametrizedChain)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ)) {b : ℝ}
    (hb : HasHalfPlaneCapacity (c.chain.maps t) b) : b = 2 * t :=
  hb.unique (chordalSLE_capacity_parametrized c t ht)


theorem chordalSLE_hcap_zero (c : CapacityParametrizedChain) :
    HasHalfPlaneCapacity (c.chain.maps 0) 0 := by
  have := chordalSLE_capacity_parametrized c 0 Set.self_mem_Ici
  rwa [mul_zero] at this


lemma continuous_sleDriving {Ω : Type*} (κ : ℝ) (B : ℝ → Ω → ℝ) (ω : Ω)
    (hcont : Continuous fun t => B t ω) : Continuous (sleDriving κ B ω) := by
  unfold sleDriving
  exact continuous_const.mul hcont


end StatMech.SLE
