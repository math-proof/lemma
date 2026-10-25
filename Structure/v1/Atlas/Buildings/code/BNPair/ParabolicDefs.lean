/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/ParabolicDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Mathlib.Tactic.Group
import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs
set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}


namespace BNPair

/-- The package of derived properties of the Bruhat decomposition needed to prove the
parabolic theorems: cells are pairwise disjoint and cover $G$, behave well under
inversion and multiplication within a parabolic, and the standard parabolics are
self-normalizing and pairwise non-conjugate. These are consequences of the BN-pair
axioms, collected here for downstream use. -/
structure BruhatProperties (bp : BNPair G M) where
  cell_disjoint : ∀ w w' : M.Group,
    (bp.bruhatCell w ∩ bp.bruhatCell w').Nonempty → w = w'
  cell_cover : ∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w
  cell_inv : ∀ (w : M.Group) (g : G),
    g ∈ bp.bruhatCell w → g⁻¹ ∈ bp.bruhatCell w⁻¹
  cell_mul_in_parabolic : ∀ (S' : Set B_idx) (w w' : M.Group),
    w ∈ bp.parabolicSubgroupW S' → w' ∈ bp.parabolicSubgroupW S' →
    ∀ g₁ g₂ : G, g₁ ∈ bp.bruhatCell w → g₂ ∈ bp.bruhatCell w' →
    ∃ u ∈ (bp.parabolicSubgroupW S' : Set M.Group), g₁ * g₂ ∈ bp.bruhatCell u
  parabolicW_injective : ∀ S₁ S₂ : Set B_idx,
    bp.parabolicSubgroupW S₁ = bp.parabolicSubgroupW S₂ → S₁ = S₂
  subgroup_over_B_eq_parabolic : ∀ P : Subgroup G, bp.B ≤ P →
    ∃ S' : Set B_idx, (P : Set G) = bp.standardParabolic S'
  normalizer_in_parabolic : ∀ S' : Set B_idx, ∀ g : G,
    (∀ x, x ∈ bp.standardParabolic S' ↔
      g * x * g⁻¹ ∈ bp.standardParabolic S') →
    g ∈ bp.standardParabolic S'
  conjugator_in_target : ∀ (S₁ S₂ : Set B_idx) (g : G),
    (fun x => g * x * g⁻¹) '' bp.standardParabolic S₁ =
      bp.standardParabolic S₂ →
    g ∈ bp.standardParabolic S₂
  cell_mul_finite : ∀ (w w' : M.Group),
    ∃ (us : Finset M.Group),
      setMul (bp.bruhatCell w) (bp.bruhatCell w') ⊆ ⋃ u ∈ us, bp.bruhatCell u

end BNPair
