/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
import Lemma.Nat.NonemptyBruhatCell
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Coxeter.Length
set_option linter.unusedSectionVars false


section CoxeterHelpers

variable {B_idx : Type*} {W : Type*} [Group W] {M : CoxeterMatrix B_idx}

/-- A **spherical BN-pair**: a BN-pair whose Weyl group $W$ is finite. Axiomatized by
existence of a longest element $w_0$ (unique, of maximal length), the fact that $w_0$
conjugates each simple reflection to another simple reflection (an involution on $S$),
and structural identities relating the torus, Borel and Levi components needed for the
opposite-parabolic / Levi-decomposition theory of finite Coxeter / Tits systems. -/
structure SphericalBNPair (G : Type*) [Group G] {B_idx : Type*}
    (M : CoxeterMatrix B_idx) extends BNPair G M where
  weylFinite : Set.Finite (Set.univ : Set M.Group)
  w₀ : M.Group
  w₀_longest : ∀ w : M.Group,
    M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length w₀
  w₀_unique : ∀ w : M.Group,
    (∀ v : M.Group, M.toCoxeterSystem.length v ≤ M.toCoxeterSystem.length w) →
    w = w₀
  w₀_conj_parabolic : ∀ s : B_idx, ∃ s' : B_idx,
    Subgroup.closure ({w₀ * M.toCoxeterSystem.simple s * w₀⁻¹} : Set M.Group) =
      Subgroup.closure ({M.toCoxeterSystem.simple s'} : Set M.Group)
  torus_eq_levi_borel : ∀ n : toBNPair.N, toBNPair.π n = w₀ →
    (toBNPair.T : Set G) =
      (toBNPair.B : Set G) ∩ ((fun s => (n : G) * s * (n : G)⁻¹) '' (toBNPair.B : Set G))
  levi_normalization : ∀ (T : Set B_idx) (n : toBNPair.N), toBNPair.π n = w₀ →
    ∀ g : G, g ∈ toBNPair.standardParabolic T →
      (fun s => g * s * g⁻¹) ''
        (toBNPair.standardParabolic T ∩
          ((fun s => (n : G) * s * (n : G)⁻¹) '' toBNPair.standardParabolic T)) ⊆
        toBNPair.standardParabolic T
  levi_weyl_group : ∀ (T : Set B_idx) (n : toBNPair.N), toBNPair.π n = w₀ →
    ∀ w : M.Group,
      w ∈ (toBNPair.parabolicSubgroupW T : Set M.Group) ↔
      toBNPair.bruhatCell w ⊆
        (toBNPair.standardParabolic T ∩
          ((fun s => (n : G) * s * (n : G)⁻¹) '' toBNPair.standardParabolic T))

end CoxeterHelpers
