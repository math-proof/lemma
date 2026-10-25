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
import Structure.v1.Atlas.Buildings.code.BNPair.SphericalCase
set_option linter.unusedSectionVars false


section CoxeterHelpers

variable {B_idx : Type*} {W : Type*} [Group W] {M : CoxeterMatrix B_idx}

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
end CoxeterHelpers
