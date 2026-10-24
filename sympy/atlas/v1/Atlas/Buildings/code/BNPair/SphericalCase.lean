/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.BNPair.Basic
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.ParabolicDefs
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

namespace SphericalBNPair

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- The **longest element** $w_0$ of a spherical Weyl group, exposed as a definition. -/
def longestElement (sbp : SphericalBNPair G M) : M.Group := sbp.w₀

variable (sbp : SphericalBNPair G M)

/-- Conjugation of a subset $S \subseteq G$ by a single element $g$: $gSg^{-1}$. -/
def conjugateSetBy (_ : SphericalBNPair G M) (g : G) (S : Set G) : Set G :=
  (fun s => g * s * g⁻¹) '' S

/-- Conjugation of $S \subseteq G$ by a chosen $N$-lift of a Weyl element $w$. -/
noncomputable def conjugateByWeylElt (sbp : SphericalBNPair G M)
    (w : M.Group) (S : Set G) : Set G :=
  sbp.conjugateSetBy (sbp.toBNPair.π_surj w).choose.val S

/-- The **opposite Borel** $B^- = n_{w_0} B n_{w_0}^{-1}$, obtained by conjugating $B$
through a chosen $N$-lift of $w_0$. -/
noncomputable def oppositeBorel (sbp : SphericalBNPair G M) : Set G :=
  sbp.conjugateByWeylElt sbp.w₀ (sbp.toBNPair.B : Set G)

/-- The **opposite parabolic** $P_T^- = n_{w_0} P_T n_{w_0}^{-1}$, for $T \subseteq S$. -/
noncomputable def oppositeParabolic (sbp : SphericalBNPair G M)
    (T : Set B_idx) : Set G :=
  sbp.conjugateByWeylElt sbp.w₀ (sbp.toBNPair.standardParabolic T)

/-- The **Levi component** $L = B \cap B^-$ of the BN-pair, the intersection of $B$ with
its opposite. -/
noncomputable def leviComponent (sbp : SphericalBNPair G M) : Set G :=
  (sbp.toBNPair.B : Set G) ∩ sbp.oppositeBorel

/-- The **Levi component of a parabolic** $L_T = P_T \cap P_T^-$, generalizing
`leviComponent` (which is the case $T = \emptyset$). -/
noncomputable def leviComponentGeneral (sbp : SphericalBNPair G M)
    (T : Set B_idx) : Set G :=
  sbp.toBNPair.standardParabolic T ∩ sbp.oppositeParabolic T

end SphericalBNPair
