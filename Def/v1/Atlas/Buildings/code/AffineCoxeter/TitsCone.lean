/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
import Mathlib.Data.Fintype.BigOperators
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The **Coxeter wall** $H_s = \{\varphi : \varphi_s = 0\}$ associated to a simple reflection $s$. -/
def coxeterWall (_M : CoxeterMatrix B) (s : B) : Set (B → ℝ) :=
  {φ | φ s = 0}

/-- The positive half-space $H_s^+ = \{\varphi : \varphi_s > 0\}$ cut out by the wall $H_s$. -/
def coxeterUpperHalf (_M : CoxeterMatrix B) (s : B) : Set (B → ℝ) :=
  {φ | φ s > 0}

/-- The negative half-space $H_s^- = \{\varphi : \varphi_s < 0\}$ cut out by the wall $H_s$. -/
def coxeterLowerHalf (_M : CoxeterMatrix B) (s : B) : Set (B → ℝ) :=
  {φ | φ s < 0}

/-- The **open fundamental chamber** $C = \bigcap_s H_s^+ = \{\varphi : \forall s, \varphi_s > 0\}$. -/
def titsFundamentalChamber (_M : CoxeterMatrix B) : Set (B → ℝ) :=
  {φ | ∀ s, φ s > 0}

/-- The **standard face** of type $I \subseteq B$: $F_I = \{\varphi : \varphi_s = 0 \text{ for } s \in I,
\ \varphi_s > 0 \text{ for } s \notin I\}$. -/
def titsFaceDual (_M : CoxeterMatrix B) (I : Finset B) : Set (B → ℝ) :=
  {φ | (∀ s ∈ I, φ s = 0) ∧ (∀ s, s ∉ I → φ s > 0)}

/-- The **contragredient action** of a simple reflection $s$ on coordinates:
$\sigma^*_s(x)_t = x_t - 2 x_s \cdot B(\alpha_s, \alpha_t)$. -/
noncomputable def dualSigma (M : CoxeterMatrix B) (s : B) (x : B → ℝ) : B → ℝ :=
  fun t => x t - 2 * x s * formVal M s t

/-- The **closed fundamental chamber** $\overline{C} = \{\varphi : \forall s, \varphi_s \ge 0\}$. -/
def titsFundamentalClosure (_M : CoxeterMatrix B) : Set (B → ℝ) :=
  {φ | ∀ s, φ s ≥ 0}

/-- The **Tits cone** $\mathcal U = W \cdot \overline{C}$: $W$-orbit of the closed fundamental
chamber under the contragredient action. -/
def titsConeSet (M : CoxeterMatrix B) : Set (B → ℝ) :=
  {x | ∃ (y : B → ℝ), (∀ s, y s ≥ 0) ∧
    ∃ (ws : List B), x = ws.foldl (fun v s => dualSigma M s v) y}

end TitsCone
